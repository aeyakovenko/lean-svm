/-
  LeanSVM.Compiler.Lower
  Native Lean 4 Monomorphic LCNF (`Lean.Compiler.LCNF.Code .pure`) → Zero-Allocation `SbfIR` Lowering.

  Key zero-overhead compilation features:
  1. Complete erasure of `Prop`, `Type`, `Unit`, and `LeanSVM.SvmState` ghost tokens (0 registers).
  2. Scalar Replacement of Aggregates (SROA) for flat structures (`Prod`, `ByteSlice`, custom structs).
  3. Unboxed representation of `SvmStep`, `Option`, `Except`, `Bool`, and flat enums (0 heap allocs).
  4. Automatic compile-time inlining of user helper functions & tail-call loop lowering (e.g. `skipAccounts`
     compiles into a tight zero-call, zero-stack sBPF loop!).
  5. Direct 1-to-1 lowering of `LeanSVM.rawLoad*`, `rawStore*`, `rawStackAlloc`, `sys*`, and all
     Lean `UInt8`/`UInt16`/`UInt32`/`UInt64`/`Bool`/`Nat` scalar operations.
-/
import Lean
import Lean.Compiler.LCNF.Basic
import Lean.Compiler.LCNF.PhaseExt
import LeanSVM.Runtime
import LeanSVM.Compiler.IR
import Std.Data.HashMap

namespace LeanSVM.Compiler

open Lean
open Lean.Compiler.LCNF

/-- Compile-time unboxed representation of any LCNF value (ZERO heap objects!). -/
inductive Val where
  | erased
  | reg (v : VReg)
  | natLit (n : Nat)
  | strLit (roOff : UInt32) (byteLen : UInt64)
  | structVal (fields : Array Val)
  | ctorVal (tag : Nat) (fields : Array Val)
  /-- Dynamically-tagged unboxed constructor (e.g., `SvmStep` / `Option` across a branch merge).
      Lives purely in virtual registers: `tag` + unboxed `payload` regs! -/
  | dynCtor (tag : VReg) (payloads : Array VReg)
  deriving Repr, Inhabited

/-- Continuation describing what to do with a function/block's return `Val`. -/
inductive RetTarget where
  /-- Top-level Solana entrypoint returning `UInt64` or `SvmStep Unit` (0 = ok, code = err). -/
  | entryExit
  /-- Inlined helper call returning into join block `contBlk` expecting a `Val` shape. -/
  | jumpTo (contBlk : BlockId) (resultSlot : IO.Ref (Option Val)) (paramRegs : IO.Ref (Array VReg))

/-- Join point descriptor for LCNF `Code.jp` / `Code.jmp` and tail-recursive self-loops. -/
structure JpInfo where
  blockId   : BlockId
  paramRegs : Array VReg -- flat VReg params of the target basic block
  paramKind : Array Bool -- true = takes a VReg, false = erased (skip)

/-- Mutable builder state for lowering one Solana entrypoint into a single optimized `Func`
    plus optional outlined internal sBPF helper functions (`call local_fn`). -/
structure LowerState where
  env             : Environment
  blocks          : Array Block := #[]
  curBlock        : BlockId := 0
  nextVReg        : Nat := 0
  rodata          : RodataPool := {}
  stackAllocBytes : Nat := 0
  /-- Reusable 8-byte stack slot for fallible outlined `SolanaM α` helper out-pointers. -/
  callRetSlotOff? : Option Int16 := none
  /-- Reusable stack arg-pack buffer `(baseOff, byteCap)` for `> 5`-arg outlined helpers. -/
  callArgsPack?   : Option (Int16 × Nat) := none
  /-- Stack of active inlined-function frames for tail-recursion loop detection. -/
  activeRecLoops  : List (Name × BlockId × Array VReg × Array Bool) := []
  /-- Outlined pure scalar helper functions (compiled once, called via 1-CU sBPF `call`). -/
  outlinedHelpers : Array Func := #[]
  outlinedNames   : Std.HashMap Name String := {}
  nextHelperId    : Nat := 0
  /-- Total call-site counts in the entrypoint's call graph (for smart inline-vs-outline heuristics!). -/
  callCounts      : Std.HashMap Name Nat := {}

abbrev LowerM := StateT LowerState (Except String)

private def freshVReg : LowerM VReg := do
  let st ← get
  let v := st.nextVReg
  set { st with nextVReg := v + 1 }
  return v

private def newBlock (params : Array VReg := #[]) : LowerM BlockId := do
  let st ← get
  let id := st.blocks.size
  set { st with blocks := st.blocks.push { id, params } }
  return id

private def switchBlock (id : BlockId) : LowerM Unit :=
  modify fun st => { st with curBlock := id }

private def emit (s : Stmt) : LowerM Unit :=
  modify fun st =>
    let bid := st.curBlock
    let blk := st.blocks[bid]!
    { st with blocks := st.blocks.set! bid { blk with stmts := blk.stmts.push s } }

private def setTerm (t : Term) : LowerM Unit :=
  modify fun st =>
    let bid := st.curBlock
    let blk := st.blocks[bid]!
    { st with blocks := st.blocks.set! bid { blk with term := t } }

private def curBlockTerminated : LowerM Bool := do
  let st ← get
  return st.blocks[st.curBlock]!.term != .unreach

private def emitConst (val : UInt64) : LowerM VReg := do
  let r ← freshVReg
  emit (.constImm r val)
  return r

private def internString (s : String) : LowerM (UInt32 × UInt64) := do
  let st ← get
  let (pool', off, len) := st.rodata.internString s
  set { st with rodata := pool' }
  return (off, len)

/-- Allocate `size` bytes (8-byte aligned) on the sBPF stack frame (`r10 - total`), 0 heap! -/
private def allocStack (size : Nat) : LowerM VReg := do
  let aligned := ((size + 7) / 8) * 8
  let st ← get
  let newTotal := st.stackAllocBytes + aligned
  if newTotal > 4096 then
    throw s!"stack allocation exceeds Solana 4KB frame limit ({newTotal} bytes)"
  set { st with stackAllocBytes := newTotal }
  let r ← freshVReg
  emit (.stackAddr r (Int16.ofInt (-(newTotal : Int))))
  return r

/-- Reuse ONE single 8-byte stack slot per function for fallible scalar helper out-pointers. -/
private def getOrAllocCallRetSlot : LowerM (VReg × Int16) := do
  let st ← get
  match st.callRetSlotOff? with
  | some sOff =>
    let r ← freshVReg
    emit (.stackAddr r sOff)
    return (r, sOff)
  | none =>
    let newTotal := st.stackAllocBytes + 8
    if newTotal > 4096 then
      throw s!"stack allocation exceeds Solana 4KB frame limit ({newTotal} bytes)"
    let sOff := Int16.ofInt (-(newTotal : Int))
    set { st with stackAllocBytes := newTotal, callRetSlotOff? := some sOff }
    let r ← freshVReg
    emit (.stackAddr r sOff)
    return (r, sOff)

/-- Reuse a stack arg-pack buffer of at least `needBytes` bytes for `> 5`-arg outlined helpers. -/
private def getOrAllocArgsPack (needBytes : Nat) : LowerM (VReg × Int16) := do
  let aligned := ((needBytes + 7) / 8) * 8
  let st ← get
  match st.callArgsPack? with
  | some (sOff, cap) =>
    if cap >= aligned then
      let r ← freshVReg
      emit (.stackAddr r sOff)
      return (r, sOff)
    else
      let newTotal := st.stackAllocBytes + aligned
      if newTotal > 4096 then
        throw s!"stack allocation exceeds Solana 4KB frame limit ({newTotal} bytes)"
      let newOff := Int16.ofInt (-(newTotal : Int))
      set { st with stackAllocBytes := newTotal, callArgsPack? := some (newOff, aligned) }
      let r ← freshVReg
      emit (.stackAddr r newOff)
      return (r, newOff)
  | none =>
    let newTotal := st.stackAllocBytes + aligned
    if newTotal > 4096 then
      throw s!"stack allocation exceeds Solana 4KB frame limit ({newTotal} bytes)"
    let newOff := Int16.ofInt (-(newTotal : Int))
    set { st with stackAllocBytes := newTotal, callArgsPack? := some (newOff, aligned) }
    let r ← freshVReg
    emit (.stackAddr r newOff)
    return (r, newOff)

/-- Materialize a `Val` as a single scalar `VReg`. -/
private def valToReg (v : Val) : LowerM VReg := do
  match v with
  | .reg r => return r
  | .natLit n => emitConst n.toUInt64
  | .erased => emitConst 0
  | .ctorVal tag #[] => emitConst tag.toUInt64
  | .ctorVal tag #[.erased] => emitConst tag.toUInt64
  | .ctorVal 0 #[a, .erased] => valToReg a
  | .ctorVal tag #[a] =>
    -- Single-field wrapper (e.g. `UInt64.mk`, `BitVec.ofFin`, `Fin.mk`)
    if tag == 0 then valToReg a else emitConst tag.toUInt64
  | .structVal #[a] => valToReg a
  | .dynCtor tag _ => return tag
  | other => throw s!"expected scalar value for register, got: {repr other}"

/-- Extract compile-time constant `Nat` if available (for `stackAlloc`, widths, etc.). -/
private def valToConstNat? : Val → Option Nat
  | .natLit n => some n
  | _ => none

/-- Look up a declaration's LCNF in `monoExt` (falling back to `baseExt`). -/
private def lookupDecl? (env : Environment) (name : Name) : Option (Decl .pure) :=
  match getDeclCore? env monoExt name with
  | some d => some d
  | none => getDeclCore? env baseExt name

/-- Determine constructor tag index from the Lean `Environment`. -/
private def getCtorIdx (env : Environment) (ctorName : Name) : Nat :=
  match env.find? ctorName with
  | some (.ctorInfo ci) => ci.cidx
  | _ =>
    match ctorName with
    | ``Bool.false => 0
    | ``Bool.true  => 1
    | ``LeanSVM.SvmStep.ok  => 0
    | ``LeanSVM.SvmStep.err => 1
    | ``Option.none => 0
    | ``Option.some => 1
    | ``Except.error => 0
    | ``Except.ok    => 1
    | _ => 0

/-- Check if `name` is an inductive constructor in `env`. -/
private def isCtor (env : Environment) (name : Name) : Bool :=
  match env.find? name with
  | some (.ctorInfo _) => true
  | _ => false

/-- Check if an LCNF type is a zero-cost erased type (`Unit`, `PUnit`, `SvmState`, `lcErased`). -/
private def isErasedType (ty : Expr) : Bool :=
  match ty.getAppFn with
  | .const n _ =>
    n == ``Unit || n == ``PUnit || n == ``LeanSVM.SvmState || n == `lcErased || n == `lcAny
  | _ => false

/-- Map `Val` of a `SolanaM Unit` / `UInt64` entrypoint return to the `r0` exit code `VReg`. -/
private def lowerEntryReturn (v : Val) : LowerM Unit := do
  match v with
  | .reg r => setTerm (.ret r)
  | .natLit n =>
    let r ← emitConst n.toUInt64
    setTerm (.ret r)
  | .erased =>
    let r ← emitConst 0
    setTerm (.ret r)
  | .ctorVal 0 _ =>
    -- `SvmStep.ok () st` -> return 0 (success!)
    let r ← emitConst 0
    setTerm (.ret r)
  | .ctorVal 1 fields =>
    -- `SvmStep.err code st` -> return `code`!
    let codeVal := fields.getD 0 .erased
    let r ← valToReg codeVal
    setTerm (.ret r)
  | .structVal fields =>
    -- e.g. `SolanaM.runEntry` returning `(code, st)`
    let r ← valToReg (fields.getD 0 .erased)
    setTerm (.ret r)
  | .dynCtor tag payloads =>
    -- Dynamic `SvmStep Unit`: if tag == 0 -> return 0, else return payloads[0]
    let okBlk ← newBlock
    let errBlk ← newBlock
    setTerm (.brCmpImm .eq tag 0 okBlk #[] errBlk #[])
    switchBlock okBlk
    let zeroReg ← emitConst 0
    setTerm (.ret zeroReg)
    switchBlock errBlk
    let errCode := payloads.getD 0 tag
    setTerm (.ret errCode)
  | other => throw s!"unsupported entrypoint return value: {repr other}"

/-- Flatten a `Val` into its runtime `VReg`s (for passing to a join point or loop header). -/
private def flattenVal (v : Val) : LowerM (Array VReg) := do
  match v with
  | .erased => return #[]
  | .reg r => return #[r]
  | .natLit n => return #[← emitConst n.toUInt64]
  | .strLit off len =>
    let rOff ← freshVReg
    emit (.constRodata rOff off)
    let rLen ← emitConst len
    return #[rOff, rLen]
  | .structVal fields =>
    let mut rs : Array VReg := #[]
    for f in fields do
      rs := rs ++ (← flattenVal f)
    return rs
  | .ctorVal tag fields =>
    if fields.isEmpty then
      return #[← emitConst tag.toUInt64]
    else
      let mut rs : Array VReg := #[← emitConst tag.toUInt64]
      for f in fields do
        rs := rs ++ (← flattenVal f)
      return rs
  | .dynCtor tag payloads =>
    return #[tag] ++ payloads

/-- Lower an LCNF `Arg .pure` using the local variable map. -/
private def lowerArg (envMap : Std.HashMap FVarId Val) (a : Arg .pure) : Val :=
  match a with
  | .fvar fid => envMap.getD fid .erased
  | .erased | .type .. => .erased

/-- Lower a known binary scalar operation (`UInt64`, `UInt32`, `UInt16`, `UInt8`, `Nat`). -/
private def lowerBinScalar (op : BinOp) (mask? : Option UInt64) (a b : Val) : LowerM Val := do
  let ra ← valToReg a
  let rb ← valToReg b
  let dst ← freshVReg
  emit (.binOp op dst ra rb)
  match mask? with
  | some mask =>
    let m ← emitConst mask
    let masked ← freshVReg
    emit (.binOp .and64 masked dst m)
    return .reg masked
  | none => return .reg dst

/-- Lean's `Nat.sub` saturates at 0, sBPF `sub64` wraps. Emit `if a < b then 0 else a - b`. -/
private def lowerSaturatingSub (a b : Val) : LowerM Val := do
  match a, b with
  | .natLit x, .natLit y => return .natLit (x - y)
  | _, _ =>
    let ra ← valToReg a
    let rb ← valToReg b
    let diff ← freshVReg
    emit (.binOp .sub64 diff ra rb)
    let jp ← freshVReg
    let underBlk ← newBlock
    let okBlk ← newBlock
    let joinBlk ← newBlock #[jp]
    setTerm (.brCmp .ult ra rb underBlk #[] okBlk #[])
    switchBlock underBlk
    let zeroReg ← emitConst 0
    setTerm (.jmp joinBlk #[zeroReg])
    switchBlock okBlk
    setTerm (.jmp joinBlk #[diff])
    switchBlock joinBlk
    return .reg jp

/-- Lean's `x / 0 = 0` and `x % 0 = x` are total, but sBPF `div`/`mod` trap on a zero
    divisor. Guard the dynamic case so a user program cannot abort the transaction
    (and lose its compute budget) on a path Lean says is well defined. -/
private def lowerDivModScalar (op : BinOp) (a b : Val) : LowerM Val := do
  let isDiv := match op with | .div64 | .div32 => true | _ => false
  match b with
  | .natLit n =>
    if n == 0 then
      if isDiv then return .reg (← emitConst 0) else return .reg (← valToReg a)
    let rb ← valToReg b
    let ra ← valToReg a
    let dst ← freshVReg
    emit (.binOp op dst ra rb)
    return .reg dst
  | _ =>
    let ra ← valToReg a
    let rb ← valToReg b
    let zeroReg ← emitConst 0
    let jp ← freshVReg
    let nzBlk ← newBlock
    let zeroBlk ← newBlock
    let joinBlk ← newBlock #[jp]
    setTerm (.brCmp .ne rb zeroReg nzBlk #[] zeroBlk #[])
    switchBlock nzBlk
    let dst ← freshVReg
    emit (.binOp op dst ra rb)
    setTerm (.jmp joinBlk #[dst])
    switchBlock zeroBlk
    let z ← if isDiv then emitConst 0 else pure ra
    setTerm (.jmp joinBlk #[z])
    switchBlock joinBlk
    return .reg jp

/-- Lower a known scalar comparison (`UInt64/32/16/8`, `Nat`, `Bool`). -/
private def lowerCmpScalar (op : CmpOp) (a b : Val) : LowerM Val := do
  let ra ← valToReg a
  let rb ← valToReg b
  let dst ← freshVReg
  emit (.cmp op dst ra rb)
  return .reg dst

/-- Lower a `LetValue.const` call if it is a recognized Lean primitive or LeanSVM hardware intrinsic.
    Returns `some val` if handled, or `none` if it should be inlined as a user/library declaration. -/
private def tryLowerPrimitive (declName : Name) (vals : Array Val) : LowerM (Option Val) := do
  -- Filter out leading erased/type args where Lean polymorphic functions pass type args
  let nonErased := vals.filter (fun v => match v with | .erased => false | _ => true)

  match declName with
  -- === LeanSVM Hardware Memory Intrinsics ===
  | ``LeanSVM.rawLoadU8 =>
    let ptr ← valToReg (vals.getD 0 .erased)
    let r ← freshVReg; emit (.load .b1 r ptr 0)
    return some (.ctorVal 0 #[.reg r, .erased])
  | ``LeanSVM.rawLoadU16 =>
    let ptr ← valToReg (vals.getD 0 .erased)
    let r ← freshVReg; emit (.load .b2 r ptr 0)
    return some (.ctorVal 0 #[.reg r, .erased])
  | ``LeanSVM.rawLoadU32 =>
    let ptr ← valToReg (vals.getD 0 .erased)
    let r ← freshVReg; emit (.load .b4 r ptr 0)
    return some (.ctorVal 0 #[.reg r, .erased])
  | ``LeanSVM.rawLoadU64 =>
    let ptr ← valToReg (vals.getD 0 .erased)
    let r ← freshVReg; emit (.load .b8 r ptr 0)
    return some (.ctorVal 0 #[.reg r, .erased])
  | ``LeanSVM.rawStoreU8 =>
    let ptr ← valToReg (vals.getD 0 .erased)
    let v   ← valToReg (vals.getD 1 .erased)
    emit (.store .b1 ptr 0 v)
    return some (.ctorVal 0 #[.erased, .erased])
  | ``LeanSVM.rawStoreU16 =>
    let ptr ← valToReg (vals.getD 0 .erased)
    let v   ← valToReg (vals.getD 1 .erased)
    emit (.store .b2 ptr 0 v)
    return some (.ctorVal 0 #[.erased, .erased])
  | ``LeanSVM.rawStoreU32 =>
    let ptr ← valToReg (vals.getD 0 .erased)
    let v   ← valToReg (vals.getD 1 .erased)
    emit (.store .b4 ptr 0 v)
    return some (.ctorVal 0 #[.erased, .erased])
  | ``LeanSVM.rawStoreU64 =>
    let ptr ← valToReg (vals.getD 0 .erased)
    let v   ← valToReg (vals.getD 1 .erased)
    emit (.store .b8 ptr 0 v)
    return some (.ctorVal 0 #[.erased, .erased])

  -- === Stack Buffer Allocation (Zero Heap!) ===
  | ``LeanSVM.rawStackAlloc =>
    let sizeVal := vals.getD 0 .erased
    let sizeNat ← match valToConstNat? sizeVal with
      | some n => pure n
      | none =>
        match sizeVal with
        | .reg vr =>
          let st ← get
          -- Build constant + alias map across lowered blocks (including constant block params!)
          let mut constMap : Std.HashMap VReg UInt64 := {}
          for blk in st.blocks do
            for s in blk.stmts do
              match s with
              | .constImm d c => constMap := constMap.insert d c
              | _ => pure ()
          for _ in [0:4] do
            for blk in st.blocks do
              for s in blk.stmts do
                match s with
                | .mov d src =>
                  if let some c := constMap.get? src then
                    constMap := constMap.insert d c
                | _ => pure ()
              if !blk.params.isEmpty then
                -- Check incoming edges to `blk`
                let mut edges : Array (Array VReg) := #[]
                for pb in st.blocks do
                  match pb.term with
                  | .jmp t a => if t == blk.id then edges := edges.push a
                  | .br _ t ta e ea | .brCmp _ _ _ t ta e ea | .brCmpImm _ _ _ t ta e ea =>
                    if t == blk.id then edges := edges.push ta
                    if e == blk.id then edges := edges.push ea
                  | _ => pure ()
                if !edges.isEmpty then
                  for k in [0:blk.params.size] do
                    let mut common? : Option UInt64 := none
                    let mut ok := true
                    for e in edges do
                      if k < e.size then
                        match constMap.get? e[k]! with
                        | some cv =>
                          match common? with
                          | none => common? := some cv
                          | some prev => if prev != cv then ok := false
                        | none => ok := false
                      else ok := false
                    if ok then
                      if let some cv := common? then
                        constMap := constMap.insert blk.params[k]! cv
          match constMap.get? vr with
          | some c => pure c.toNat
          | none =>
            let mut info := ""
            for blk in st.blocks do
              if blk.params.contains vr then
                info := info ++ s!" paramOf(bb{blk.id},params={blk.params})"
              for s in blk.stmts do
                if s.defReg? == some vr then
                  info := info ++ s!" stmt({reprStr s})"
            throw s!"LeanSVM.stackAlloc requires a compile-time constant byte size (got reg {vr}{info} in blocks={st.blocks.size})"
        | other => throw s!"LeanSVM.stackAlloc requires a compile-time constant byte size (got {repr other})"
    let ptrReg ← allocStack sizeNat
    return some (.ctorVal 0 #[.reg ptrReg, .erased])

  -- === Solana Syscall Intrinsics ===
  | ``LeanSVM.sysLog =>
    match vals.getD 0 .erased with
    | .strLit off len =>
      let rPtr ← freshVReg; emit (.constRodata rPtr off)
      let rLen ← emitConst len
      emit (.syscall none "sol_log_" #[rPtr, rLen])
      return some (.ctorVal 0 #[.erased, .erased])
    | _ => throw "LeanSVM.log requires a compile-time String literal (zero heap allocation)"
  | ``LeanSVM.sysLog64 =>
    let r0 ← valToReg (vals.getD 0 .erased)
    let r1 ← valToReg (vals.getD 1 .erased)
    let r2 ← valToReg (vals.getD 2 .erased)
    let r3 ← valToReg (vals.getD 3 .erased)
    let r4 ← valToReg (vals.getD 4 .erased)
    emit (.syscall none "sol_log_64_" #[r0, r1, r2, r3, r4])
    return some (.ctorVal 0 #[.erased, .erased])
  | ``LeanSVM.sysLogComputeUnits =>
    emit (.syscall none "sol_log_compute_units_" #[])
    return some (.ctorVal 0 #[.erased, .erased])
  | ``LeanSVM.sysMemcpy =>
    let r0 ← valToReg (vals.getD 0 .erased)
    let r1 ← valToReg (vals.getD 1 .erased)
    let r2 ← valToReg (vals.getD 2 .erased)
    emit (.syscall none "sol_memcpy_" #[r0, r1, r2])
    return some (.ctorVal 0 #[.erased, .erased])
  | ``LeanSVM.sysMemset =>
    let r0 ← valToReg (vals.getD 0 .erased)
    let r1 ← valToReg (vals.getD 1 .erased)
    let r2 ← valToReg (vals.getD 2 .erased)
    emit (.syscall none "sol_memset_" #[r0, r1, r2])
    return some (.ctorVal 0 #[.erased, .erased])
  | ``LeanSVM.sysMemcmp =>
    let r0 ← valToReg (vals.getD 0 .erased)
    let r1 ← valToReg (vals.getD 1 .erased)
    let r2 ← valToReg (vals.getD 2 .erased)
    let r3 ← valToReg (vals.getD 3 .erased)
    emit (.syscall none "sol_memcmp_" #[r0, r1, r2, r3])
    return some (.ctorVal 0 #[.erased, .erased])
  | ``LeanSVM.sysSha256 =>
    let r0 ← valToReg (vals.getD 0 .erased)
    let r1 ← valToReg (vals.getD 1 .erased)
    let r2 ← valToReg (vals.getD 2 .erased)
    let res ← freshVReg
    emit (.syscall (some res) "sol_sha256" #[r0, r1, r2])
    return some (.ctorVal 0 #[.reg res, .erased])
  | ``LeanSVM.sysGetClock =>
    let r0 ← valToReg (vals.getD 0 .erased)
    let res ← freshVReg
    emit (.syscall (some res) "sol_get_clock_sysvar" #[r0])
    return some (.ctorVal 0 #[.reg res, .erased])
  | ``LeanSVM.sysInvokeSignedC =>
    let r0 ← valToReg (vals.getD 0 .erased)
    let r1 ← valToReg (vals.getD 1 .erased)
    let r2 ← valToReg (vals.getD 2 .erased)
    let r3 ← valToReg (vals.getD 3 .erased)
    let r4 ← valToReg (vals.getD 4 .erased)
    let res ← freshVReg
    emit (.syscall (some res) "sol_invoke_signed_c" #[r0, r1, r2, r3, r4])
    return some (.ctorVal 0 #[.reg res, .erased])

  -- === UInt64 Arithmetic & Bitwise ===
  | ``UInt64.add => some <$> lowerBinScalar .add64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.sub => some <$> lowerBinScalar .sub64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.mul => some <$> lowerBinScalar .mul64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.div => some <$> lowerDivModScalar .div64 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.mod => some <$> lowerDivModScalar .mod64 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.land => some <$> lowerBinScalar .and64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.lor  => some <$> lowerBinScalar .or64  none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.xor  => some <$> lowerBinScalar .xor64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.shiftLeft  => some <$> lowerBinScalar .lsh64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.shiftRight => some <$> lowerBinScalar .rsh64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.decEq | `UInt64.beq => some <$> lowerCmpScalar .eq  (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.decLt | `UInt64.blt => some <$> lowerCmpScalar .ult (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt64.decLe | `UInt64.ble => some <$> lowerCmpScalar .ule (vals.getD 0 .erased) (vals.getD 1 .erased)

  -- === UInt32 Arithmetic & Bitwise ===
  | ``UInt32.add => some <$> lowerBinScalar .add32 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.sub => some <$> lowerBinScalar .sub32 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.mul => some <$> lowerBinScalar .mul32 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.div => some <$> lowerDivModScalar .div32 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.mod => some <$> lowerDivModScalar .mod32 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.land => some <$> lowerBinScalar .and32 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.lor  => some <$> lowerBinScalar .or32  none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.xor  => some <$> lowerBinScalar .xor32 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.shiftLeft  => some <$> lowerBinScalar .lsh32 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.shiftRight => some <$> lowerBinScalar .rsh32 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.decEq | `UInt32.beq => some <$> lowerCmpScalar .eq  (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.decLt | `UInt32.blt => some <$> lowerCmpScalar .ult (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt32.decLe | `UInt32.ble => some <$> lowerCmpScalar .ule (vals.getD 0 .erased) (vals.getD 1 .erased)

  -- === UInt16 Arithmetic & Bitwise ===
  | ``UInt16.add => some <$> lowerBinScalar .add64 (some 0xFFFF) (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.sub => some <$> lowerBinScalar .sub64 (some 0xFFFF) (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.mul => some <$> lowerBinScalar .mul64 (some 0xFFFF) (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.div => some <$> lowerDivModScalar .div64 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.mod => some <$> lowerDivModScalar .mod64 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.land => some <$> lowerBinScalar .and64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.lor  => some <$> lowerBinScalar .or64  none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.xor  => some <$> lowerBinScalar .xor64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.decEq | `UInt16.beq => some <$> lowerCmpScalar .eq  (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.decLt | `UInt16.blt => some <$> lowerCmpScalar .ult (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt16.decLe | `UInt16.ble => some <$> lowerCmpScalar .ule (vals.getD 0 .erased) (vals.getD 1 .erased)

  -- === UInt8 Arithmetic & Bitwise ===
  | ``UInt8.add => some <$> lowerBinScalar .add64 (some 0xFF) (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.sub => some <$> lowerBinScalar .sub64 (some 0xFF) (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.mul => some <$> lowerBinScalar .mul64 (some 0xFF) (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.div => some <$> lowerDivModScalar .div64 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.mod => some <$> lowerDivModScalar .mod64 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.land => some <$> lowerBinScalar .and64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.lor  => some <$> lowerBinScalar .or64  none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.xor  => some <$> lowerBinScalar .xor64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.decEq | `UInt8.beq => some <$> lowerCmpScalar .eq  (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.decLt | `UInt8.blt => some <$> lowerCmpScalar .ult (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``UInt8.decLe | `UInt8.ble => some <$> lowerCmpScalar .ule (vals.getD 0 .erased) (vals.getD 1 .erased)

  -- === Scalar Nat ops (for loop indices / small literals) ===
  | ``Nat.add => some <$> lowerBinScalar .add64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Nat.sub => some <$> lowerSaturatingSub (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Nat.mul => some <$> lowerBinScalar .mul64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Nat.div => some <$> lowerDivModScalar .div64 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Nat.mod => some <$> lowerDivModScalar .mod64 (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Nat.beq | ``Nat.decEq => some <$> lowerCmpScalar .eq  (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Nat.ble | ``Nat.decLe => some <$> lowerCmpScalar .ule (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Nat.blt | ``Nat.decLt => some <$> lowerCmpScalar .ult (vals.getD 0 .erased) (vals.getD 1 .erased)

  -- === Integer Width Conversions (Zero-cost widening; mask only when narrowing!) ===
  | ``UInt8.toUInt16 | ``UInt8.toUInt32 | ``UInt8.toUInt64 | ``UInt8.toNat
  | ``UInt16.toUInt32 | ``UInt16.toUInt64 | ``UInt16.toNat
  | ``UInt32.toUInt64 | ``UInt32.toNat
  | ``UInt64.toNat | ``UInt64.toUSize | ``USize.toUInt64 =>
    return some (vals.getD 0 .erased)
  | ``UInt64.ofNat | ``UInt64.ofNatTruncate =>
    match vals.getD 0 .erased with
    | .natLit n => return some (.reg (← emitConst n.toUInt64))
    | v => return some v
  | ``UInt32.ofNat | ``UInt32.ofNatTruncate | ``UInt64.toUInt32 =>
    match vals.getD 0 .erased with
    | .natLit n => return some (.reg (← emitConst n.toUInt32.toUInt64))
    | v =>
      let r ← valToReg v
      let m ← emitConst 0xFFFFFFFF
      let dst ← freshVReg; emit (.binOp .and64 dst r m)
      return some (.reg dst)
  | ``UInt16.ofNat | ``UInt16.ofNatTruncate | ``UInt64.toUInt16 | ``UInt32.toUInt16 =>
    match vals.getD 0 .erased with
    | .natLit n => return some (.reg (← emitConst n.toUInt16.toUInt64))
    | v =>
      let r ← valToReg v
      let m ← emitConst 0xFFFF
      let dst ← freshVReg; emit (.binOp .and64 dst r m)
      return some (.reg dst)
  | ``UInt8.ofNat | ``UInt8.ofNatTruncate | ``UInt64.toUInt8 | ``UInt32.toUInt8 | ``UInt16.toUInt8 =>
    match vals.getD 0 .erased with
    | .natLit n => return some (.reg (← emitConst n.toUInt8.toUInt64))
    | v =>
      let r ← valToReg v
      let m ← emitConst 0xFF
      let dst ← freshVReg; emit (.binOp .and64 dst r m)
      return some (.reg dst)

  -- === Boolean & Decidable Operations ===
  | ``Bool.true  => return some (.reg (← emitConst 1))
  | ``Bool.false => return some (.reg (← emitConst 0))
  | ``Bool.not =>
    let r ← valToReg (vals.getD 0 .erased)
    let dst ← freshVReg
    emit (.binImm .xor64 dst r 1)
    return some (.reg dst)
  | ``Bool.and => some <$> lowerBinScalar .and64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Bool.or  => some <$> lowerBinScalar .or64  none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Bool.xor => some <$> lowerBinScalar .xor64 none (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Bool.decEq | ``Bool.beq => some <$> lowerCmpScalar .eq (vals.getD 0 .erased) (vals.getD 1 .erased)
  | ``Decidable.decide | ``instDecidableEqBool | ``instDecidableNot =>
    -- In mono LCNF, `Decidable` is represented as `Bool` (0 or 1)!
    if declName == ``instDecidableNot then
      let r ← valToReg (nonErased.getD 0 .erased)
      let dst ← freshVReg
      emit (.binImm .xor64 dst r 1)
      return some (.reg dst)
    else
      return some (nonErased.getD 0 .erased)

  -- === Polymorphic BEq / bne / Ord helpers that occasionally remain in mono LCNF ===
  | ``bne =>
    -- `bne α inst a b` -> `a != b`
    let n := nonErased.size
    if n >= 2 then
      some <$> lowerCmpScalar .ne nonErased[n - 2]! nonErased[n - 1]!
    else return none

  -- === Zero-cost Unit / PUnit / SvmState constructors ===
  | ``Unit.unit | ``PUnit.unit => return some .erased
  | ``LeanSVM.SvmState.mk => return some .erased

  | _ => return none

private def peelForallTy (e : Expr) : Expr :=
  match e with
  | .forallE _ _ b _ => peelForallTy b
  | other => other

private def isScalarType (ty : Expr) : Bool :=
  match (peelForallTy ty).getAppFn with
  | .const n _ =>
    n == ``UInt64 || n == ``UInt32 || n == ``UInt16 || n == ``UInt8 || n == ``Bool || n == ``Nat
  | _ => false

private def isSvmStepUnitType (ty : Expr) : Bool :=
  let ret := peelForallTy ty
  match ret.getAppFn, ret.getAppArgs with
  | .const n _, #[arg] =>
    n == ``LeanSVM.SvmStep && (isErasedType arg)
  | _, _ => false

private def isSvmStepScalarOrUnitType (ty : Expr) : Bool :=
  let ret := peelForallTy ty
  match ret.getAppFn, ret.getAppArgs with
  | .const n _, #[arg] =>
    n == ``LeanSVM.SvmStep && (isErasedType arg || isScalarType arg)
  | _, _ => false

private def isSvmStepScalarType (ty : Expr) : Bool :=
  let ret := peelForallTy ty
  match ret.getAppFn, ret.getAppArgs with
  | .const n _, #[arg] =>
    n == ``LeanSVM.SvmStep && isScalarType arg
  | _, _ => false

private def isSvmStepType (ty : Expr) : Bool :=
  match (peelForallTy ty).getAppFn with
  | .const n _ => n == ``LeanSVM.SvmStep
  | _ => false

/-- Conservatively check whether `c` can transitively produce `SvmStep.err`.
    Fail-safe by default: returns `true` on `SvmStep.err`, `SolanaM.fail`, `SolanaM.require`,
    `sysInvokeSignedC`, unknown/external `SvmStep` functions, dynamic closure calls, or fuel
    exhaustion. Recurses into all called LCNF declarations so wrappers like
    `checkDexVaultAndMint` (which only call `checkTokenProg` / `requireKeyEq`) are ALWAYS
    classified as fallible! -/
private partial def codeMayFail (env : Environment) (c : Code .pure)
    (visited : Std.HashSet Name := {}) (fuel : Nat := 32) : Bool :=
  if fuel == 0 then true
  else match c with
  | .let d k =>
    let declMayFail : Bool :=
      match d.value with
      | .const n _ _ _ =>
        if n == ``LeanSVM.SvmStep.err || n == ``LeanSVM.SolanaM.fail ||
           n == ``LeanSVM.SolanaM.require || n == ``LeanSVM.sysInvokeSignedC then
          true
        else if n == ``LeanSVM.SvmStep.ok || isCtor env n then
          false
        else if n == ``LeanSVM.rawLoadU8 || n == ``LeanSVM.rawLoadU16 ||
                n == ``LeanSVM.rawLoadU32 || n == ``LeanSVM.rawLoadU64 ||
                n == ``LeanSVM.rawStoreU8 || n == ``LeanSVM.rawStoreU16 ||
                n == ``LeanSVM.rawStoreU32 || n == ``LeanSVM.rawStoreU64 ||
                n == ``LeanSVM.rawStackAlloc || n == ``LeanSVM.sysLog ||
                n == ``LeanSVM.sysLog64 || n == ``LeanSVM.sysLogComputeUnits ||
                n == ``LeanSVM.sysMemcpy || n == ``LeanSVM.sysMemset ||
                n == ``LeanSVM.sysGetClock || n == ``LeanSVM.sysSha256 then
          false
        else if visited.contains n then
          false
        else
          match lookupDecl? env n with
          | some subDecl =>
            match subDecl.value with
            | .code subBody => codeMayFail env subBody (visited.insert n) (fuel - 1)
            | .extern _ => isSvmStepType subDecl.type
          | none =>
            match env.find? n with
            | some ci => isSvmStepType ci.type
            | none => true
      | .fvar _ args => !args.isEmpty
      | _ => false
    declMayFail || codeMayFail env k visited fuel
  | .jp d k => codeMayFail env d.value visited fuel || codeMayFail env k visited fuel
  | .fun d k _ => codeMayFail env d.value visited fuel || codeMayFail env k visited fuel
  | .cases cs => cs.alts.any fun a =>
    match a with
    | .alt _ _ body _ | .default body | .ctorAlt _ body _ => codeMayFail env body visited fuel
  | _ => false

private def shouldInlineSmallHelper (callCounts : Std.HashMap Name Nat) (n : Name) : Bool :=
  -- Small hot SDK helpers (`nextCursor`, `pubkeyEq`, `pubkeyCopy`) inline when used <= 4 times
  -- for maximum CU speed on tight programs, and outline when used > 4 times for tiny `.so` size!
  let isSmallHot :=
    n == `LeanSVM.AccountView.nextCursor ||
    n == `LeanSVM.pubkeyEq ||
    n == `LeanSVM.pubkeyCopy
  isSmallHot && callCounts.getD n 0 <= 4

private partial def countCodeCalls (env : Environment) (c : Code .pure)
    (counts : Std.HashMap Name Nat) (visited : Std.HashSet Name) (depth : Nat) :
    Std.HashMap Name Nat × Std.HashSet Name :=
  if depth == 0 then (counts, visited)
  else match c with
  | .let d k =>
    let (counts1, vis1) :=
      match d.value with
      | .const n _ _ _ =>
        let counts' := counts.insert n (counts.getD n 0 + 1)
        if !visited.contains n then
          let vis' := visited.insert n
          match lookupDecl? env n with
          | some decl =>
            match decl.value with
            | .code body => countCodeCalls env body counts' vis' (depth - 1)
            | .extern _ => (counts', vis')
          | none => (counts', vis')
        else (counts', visited)
      | _ => (counts, visited)
    countCodeCalls env k counts1 vis1 depth
  | .jp d k =>
    let (c1, v1) := countCodeCalls env d.value counts visited depth
    countCodeCalls env k c1 v1 depth
  | .fun d k _ =>
    let (c1, v1) := countCodeCalls env d.value counts visited depth
    countCodeCalls env k c1 v1 depth
  | .cases cs =>
    cs.alts.foldl (init := (counts, visited)) fun (accC, accV) a =>
      match a with
      | .alt _ _ body _ | .default body | .ctorAlt _ body _ =>
        countCodeCalls env body accC accV depth
  | _ => (counts, visited)

private partial def codeSize (c : Code .pure) : Nat :=
  match c with
  | .let _ k => 1 + codeSize k
  | .jp d k => 1 + codeSize d.value + codeSize k
  | .fun d k _ => 1 + codeSize d.value + codeSize k
  | .cases cs =>
    cs.alts.foldl (init := 1) fun acc a =>
      acc + match a with
        | .alt _ _ body _ | .default body | .ctorAlt _ body _ => codeSize body
  | _ => 1

private partial def containsSyscall (c : Code .pure) : Bool :=
  match c with
  | .let d k =>
    let hit := match d.value with
      | .const n _ _ _ =>
        n == ``LeanSVM.sysGetClock || n == ``LeanSVM.sysSha256 || n == ``LeanSVM.sysInvokeSignedC
      | _ => false
    hit || containsSyscall k
  | .jp d k => containsSyscall d.value || containsSyscall k
  | .fun d k _ => containsSyscall d.value || containsSyscall k
  | .cases cs => cs.alts.any fun a =>
    match a with
    | .alt _ _ body _ | .default body | .ctorAlt _ body _ => containsSyscall body
  | _ => false

/-- Smart compiler-driven outlining decision:
    Automatically outlines shared helpers (`calls >= 2 && (size >= 18 || containsSyscall)`)
    and large handlers (`size >= 48`) into 1-CU sBPF `call` frames WITHOUT `@[noinline]`! -/
private def shouldAutoOutline (env : Environment) (callCounts : Std.HashMap Name Nat) (d : Decl .pure) : Bool :=
  let n := d.name
  let ns := n.toString
  if shouldInlineSmallHelper callCounts n then false
  else if ns.startsWith "UInt" || ns.startsWith "Bool." || ns.startsWith "Nat." ||
          ns.startsWith "Decidable." || ns.startsWith "LeanSVM.raw" || ns.startsWith "LeanSVM.sys" ||
          ns.startsWith "LeanSVM.load" || ns.startsWith "LeanSVM.store" ||
          ns.startsWith "LeanSVM.checked" || ns.startsWith "LeanSVM.SolanaM." ||
          ns.startsWith "LeanSVM.stackAlloc" || ns.startsWith "LeanSVM.Input.parse" ||
          (ns.startsWith "LeanSVM.AccountView." && n != `LeanSVM.AccountView.nextCursor) then
    false
  else if Lean.Compiler.hasNoInlineAttribute env n ||
          ns.endsWith "div128Loop" || ns.endsWith "isqrt64" then
    true
  else
    match d.value with
    | .code body =>
      let sz := codeSize body
      let cnt := callCounts.getD n 0
      (cnt >= 5 && sz >= 12) || (cnt >= 2 && (sz >= 16 || containsSyscall body)) || sz >= 44
    | .extern _ => false

private def nonErasedParamCount (d : Decl .pure) : Nat :=
  d.params.foldl (fun c p => if isErasedType p.type then c else c + 1) 0

private def isInfallibleSvmHelper (env : Environment) (d : Decl .pure) : Bool :=
  let cnt := nonErasedParamCount d
  if cnt > 12 then false
  else
    match d.value with
    | .code body => isSvmStepScalarType d.type && !codeMayFail env body
    | _ => false

private def isFallibleSvmHelper (env : Environment) (d : Decl .pure) : Bool :=
  let cnt := nonErasedParamCount d
  if cnt > 12 then false
  else
    match d.value with
    | .code body => isSvmStepScalarType d.type && codeMayFail env body
    | _ => false

private def isScalarHelper (d : Decl .pure) : Bool :=
  let cnt := nonErasedParamCount d
  cnt >= 1 && cnt <= 12 && isScalarType d.type

private def isSvmUnitHelper (d : Decl .pure) : Bool :=
  let cnt := nonErasedParamCount d
  cnt <= 12 && isSvmStepUnitType d.type

/-- Lower LCNF `Code .pure` into `SbfIR` blocks.
    `onReturn` handles `.return fvar` (either exiting the entrypoint or jumping to an inlined caller's continuation). -/
partial def lowerCode
    (code : Code .pure)
    (envMap : Std.HashMap FVarId Val)
    (jpMap : Std.HashMap FVarId JpInfo)
    (onReturn : Val → LowerM Unit)
    (fuel : Nat := 128) : LowerM Unit := do
  if fuel == 0 then
    throw "inlining/lowering fuel exhausted (possible unbounded non-tail recursion)"
  let env := (← get).env

  match code with
  | .return fid =>
    let v := envMap.getD fid .erased
    onReturn v

  | .unreach _ =>
    setTerm .unreach

  | .let decl k =>
    let val ← match decl.value with
      | .erased => pure .erased
      | .lit litVal =>
        match litVal with
        | .nat n     => pure (.natLit n)
        | .uint8 v   => pure (.reg (← emitConst v.toUInt64))
        | .uint16 v  => pure (.reg (← emitConst v.toUInt64))
        | .uint32 v  => pure (.reg (← emitConst v.toUInt64))
        | .uint64 v  => pure (.reg (← emitConst v))
        | .usize v   => pure (.reg (← emitConst v))
        | .str s     =>
          let (off, len) ← internString s
          pure (.strLit off len)
      | .proj _ idx structFid _ =>
        match envMap.getD structFid .erased with
        | .structVal fields => pure (fields.getD idx .erased)
        | .ctorVal _ fields => pure (fields.getD idx .erased)
        | .dynCtor _ payloads => pure (.reg (payloads.getD idx 0))
        | .erased => pure .erased
        | .reg r =>
          if idx == 0 then pure (.reg r)
          else throw s!"cannot project field {idx} from scalar register v{r}"
        | other => throw s!"cannot project field {idx} from {repr other}"
      | .fvar fid args =>
        if args.isEmpty then
          pure (envMap.getD fid .erased)
        else
          throw s!"dynamic closure call to fvar {fid.name} is not supported in zero-allocation sBPF"
      | .const declName _ args _ =>
        let argVals := args.map (lowerArg envMap)
        -- 1. Check recognized primitives & hardware intrinsics first
        match ← tryLowerPrimitive declName argVals with
        | some v => pure v
        | none =>
          -- 2. Check if it is an inductive constructor (zero-heap SROA / unboxed ctorVal!)
          if isCtor env declName then
            let tag := getCtorIdx env declName
            -- Count how many constructors this inductive has
            let numCtors :=
              match env.find? declName with
              | some (.ctorInfo ci) =>
                match env.find? ci.induct with
                | some (.inductInfo ii) => ii.ctors.length
                | _ => 2
              | _ => 2
            -- Strip erased type-parameter prefix args of constructor (`ci.numParams`)
            let numParams :=
              match env.find? declName with
              | some (.ctorInfo ci) => ci.numParams
              | _ => 0
            let fields := argVals.extract numParams argVals.size
            if numCtors == 1 then
              pure (.structVal fields)
            else
              pure (.ctorVal tag fields)
          else
            -- 3. Check for tail-recursive self-call inside a recursive loop!
            let recLoop? := (← get).activeRecLoops.find? (fun e => e.1 == declName)
            match recLoop?, k with
            | some (_, loopBlk, _, paramKinds), .return retFid =>
              if retFid == decl.fvarId then
                -- TAIL CALL! Jump straight back to `loopBlk` with updated arguments (0 call, 0 stack!)
                let mut jmpArgs : Array VReg := #[]
                for idx in [0:paramKinds.size] do
                  if paramKinds[idx]! then
                    let v := argVals.getD idx .erased
                    jmpArgs := jmpArgs.push (← valToReg v)
                setTerm (.jmp loopBlk jmpArgs)
                return ()
              else
                throw s!"non-tail recursive call to {declName} is not supported in zero-stack sBPF"
            | some _, _ =>
              throw s!"non-tail recursive call to {declName} (continuation is not return)"
            | none, _ =>
              -- 4. Outline pure scalar or `SolanaM Unit` `@[noinline]` helpers as real sBPF internal functions (`call`)
              match lookupDecl? env declName with
              | some calleeDecl =>
                match calleeDecl.value with
                | .code calleeBody =>
                  let cc := (← get).callCounts
                  let autoOut := shouldAutoOutline env cc calleeDecl
                  let isSvmUnit := isSvmUnitHelper calleeDecl
                  let isInfallibleSvm := isInfallibleSvmHelper env calleeDecl
                  let isFallibleSvm := isFallibleSvmHelper env calleeDecl
                  let isScalar := isScalarHelper calleeDecl
                  if autoOut && (isScalar || isSvmUnit || isInfallibleSvm || isFallibleSvm) then
                    let numValArgs := nonErasedParamCount calleeDecl
                    let totalPassSlots := numValArgs + (if isFallibleSvm then 1 else 0)
                    let usesPack := totalPassSlots > 5
                    let packBytes := (totalPassSlots - 4) * 8
                    let retPackOff : Int16 := Int16.ofInt ((numValArgs - 4) * 8)
                    let fnLabel ← match (← get).outlinedNames.get? declName with
                      | some lbl => pure lbl
                      | none =>
                        let curSt ← get
                        let idx := curSt.nextHelperId
                        let lbl := s!"fn_{idx}_"
                        set { curSt with
                          nextHelperId := idx + 1
                          outlinedNames := curSt.outlinedNames.insert declName lbl
                        }
                        let savedBlocks := (← get).blocks
                        let savedCurBlk := (← get).curBlock
                        let savedNextVReg := (← get).nextVReg
                        let savedStack := (← get).stackAllocBytes
                        let savedRetSlot := (← get).callRetSlotOff?
                        let savedArgsPack := (← get).callArgsPack?
                        let savedLoops := (← get).activeRecLoops
                        modify fun st => { st with
                          blocks := #[], curBlock := 0, nextVReg := 0,
                          stackAllocBytes := 0, callRetSlotOff? := none,
                          callArgsPack? := none, activeRecLoops := []
                        }
                        let hEntryBlk ← newBlock #[]
                        switchBlock hEntryBlk
                        let mut hParams : Array VReg := #[]
                        let mut hValRegs : Array VReg := #[]
                        let mut hKinds : Array Bool := #[]
                        let mut hEnv : Std.HashMap FVarId Val := {}
                        let mut packPtrReg? : Option VReg := none
                        if usesPack then
                          -- First 4 value params arrive in `r1..r4`; `r5` is stack arg-pack pointer!
                          let mut valIdx : Nat := 0
                          let mut overflowParams : Array (FVarId × Nat) := #[]
                          for p in calleeDecl.params do
                            if isErasedType p.type then
                              hKinds := hKinds.push false
                              hEnv := hEnv.insert p.fvarId .erased
                            else
                              hKinds := hKinds.push true
                              if valIdx < 4 then
                                let pr ← freshVReg
                                hParams := hParams.push pr
                                hValRegs := hValRegs.push pr
                                hEnv := hEnv.insert p.fvarId (.reg pr)
                              else
                                overflowParams := overflowParams.push (p.fvarId, valIdx - 4)
                              valIdx := valIdx + 1
                          let packReg ← freshVReg
                          hParams := hParams.push packReg
                          packPtrReg? := some packReg
                          for (fid, slotIdx) in overflowParams do
                            let vr ← freshVReg
                            emit (.load .b8 vr packReg (Int16.ofInt (slotIdx * 8)))
                            hValRegs := hValRegs.push vr
                            hEnv := hEnv.insert fid (.reg vr)
                        else
                          for p in calleeDecl.params do
                            if isErasedType p.type then
                              hKinds := hKinds.push false
                              hEnv := hEnv.insert p.fvarId .erased
                            else
                              let pr ← freshVReg
                              hParams := hParams.push pr
                              hValRegs := hValRegs.push pr
                              hKinds := hKinds.push true
                              hEnv := hEnv.insert p.fvarId (.reg pr)
                        -- For fallible `SolanaM α` helpers, determine `(outPtrReg, outOff)`!
                        let outPtrInfo? : Option (VReg × Int16) ← if isFallibleSvm then
                            match packPtrReg? with
                            | some pr => pure (some (pr, retPackOff))
                            | none =>
                              let op ← freshVReg
                              hParams := hParams.push op
                              pure (some (op, 0))
                          else pure none
                        let helperRet : Val → LowerM Unit :=
                          if isSvmUnit then lowerEntryReturn
                          else if isInfallibleSvm then fun rv => do
                            let r ← extractLoopVal rv
                            setTerm (.ret r)
                          else if let some (outPtrReg, outOff) := outPtrInfo? then fun rv => do
                            match rv with
                            | .ctorVal 0 fields =>
                              let vr ← valToReg (fields.getD 0 .erased)
                              emit (.store .b8 outPtrReg outOff vr)
                              let z ← emitConst 0
                              setTerm (.ret z)
                            | .ctorVal 1 fields =>
                              let er ← valToReg (fields.getD 0 .erased)
                              setTerm (.ret er)
                            | .dynCtor tag payloads =>
                              let okB ← newBlock
                              let errB ← newBlock
                              setTerm (.brCmpImm .eq tag 0 okB #[] errB #[])
                              switchBlock okB
                              emit (.store .b8 outPtrReg outOff (payloads.getD 0 tag))
                              let z ← emitConst 0
                              setTerm (.ret z)
                              switchBlock errB
                              setTerm (.ret (payloads.getD 0 tag))
                            | other =>
                              let vr ← valToReg other
                              emit (.store .b8 outPtrReg outOff vr)
                              let z ← emitConst 0
                              setTerm (.ret z)
                          else fun rv => do let r ← valToReg rv; setTerm (.ret r)
                        if containsConst calleeBody declName then
                          let mut loopParams : Array VReg := #[]
                          let mut loopEnv : Std.HashMap FVarId Val := {}
                          for p in calleeDecl.params do
                            if isErasedType p.type then
                              loopEnv := loopEnv.insert p.fvarId .erased
                            else
                              let lr ← freshVReg
                              loopParams := loopParams.push lr
                              loopEnv := loopEnv.insert p.fvarId (.reg lr)
                          let lBlk ← newBlock loopParams
                          setTerm (.jmp lBlk hValRegs)
                          switchBlock lBlk
                          modify fun st => { st with activeRecLoops := [(declName, lBlk, loopParams, hKinds)] }
                          lowerCode calleeBody loopEnv {} helperRet (fuel - 1)
                        else
                          lowerCode calleeBody hEnv {} helperRet (fuel - 1)
                        let hSt ← get
                        let helperFunc : Func := {
                          name := declName.toString
                          labelPrefix := lbl
                          isEntry := false
                          params := hParams
                          blocks := hSt.blocks
                          stackAllocBytes := hSt.stackAllocBytes
                          nextVReg := hSt.nextVReg
                        }
                        modify fun st => { st with
                          blocks := savedBlocks
                          curBlock := savedCurBlk
                          nextVReg := savedNextVReg
                          stackAllocBytes := savedStack
                          callRetSlotOff? := savedRetSlot
                          callArgsPack? := savedArgsPack
                          activeRecLoops := savedLoops
                          outlinedHelpers := st.outlinedHelpers.push helperFunc
                        }
                        pure lbl
                    let mut callArgs : Array VReg := #[]
                    for idx in [0:calleeDecl.params.size] do
                      if !isErasedType calleeDecl.params[idx]!.type then
                        callArgs := callArgs.push (← valToReg (argVals.getD idx .erased))
                    let (passArgs, outSlotOff?) : Array VReg × Option Int16 ←
                      if usesPack then
                        let (packPtrReg, packBaseOff) ← getOrAllocArgsPack packBytes
                        for idx in [4:callArgs.size] do
                          let sOff := Int16.ofInt (packBaseOff.toInt + ((idx - 4) * 8 : Int))
                          emit (.storeStack .b8 sOff callArgs[idx]!)
                        let regArgs := #[callArgs[0]!, callArgs[1]!, callArgs[2]!, callArgs[3]!, packPtrReg]
                        let rOff? := if isFallibleSvm then some (Int16.ofInt (packBaseOff.toInt + retPackOff.toInt)) else none
                        pure (regArgs, rOff?)
                      else if isFallibleSvm then
                        let (outPtrReg, outOff) ← getOrAllocCallRetSlot
                        pure (callArgs.push outPtrReg, some outOff)
                      else
                        pure (callArgs, none)
                    if isSvmUnit && !codeMayFail env calleeBody then
                      -- Transitively-verified infallible `SolanaM Unit` helper: 1-instruction `call`, ZERO error check!
                      emit (.call none fnLabel passArgs)
                      pure (.ctorVal 0 #[.erased, .erased])
                    else if isFallibleSvm then
                      -- Fallible `SolanaM α` helper: check `r0 == 0`, load result from stack out-slot!
                      let outSlotOff := outSlotOff?.getD 0
                      let resReg ← freshVReg
                      emit (.call (some resReg) fnLabel passArgs)
                      let okBlk ← newBlock #[]
                      let errBlk ← newBlock #[]
                      setTerm (.brCmpImm .eq resReg 0 okBlk #[] errBlk #[])
                      switchBlock errBlk
                      let envErr := envMap.insert decl.fvarId (.ctorVal 1 #[.reg resReg, .erased])
                      lowerCode k envErr jpMap onReturn fuel
                      switchBlock okBlk
                      let valReg ← freshVReg
                      emit (.loadStack .b8 valReg outSlotOff)
                      let envOk := envMap.insert decl.fvarId (.ctorVal 0 #[.reg valReg, .erased])
                      lowerCode k envOk jpMap onReturn fuel
                      return ()
                    else
                    let resReg ← freshVReg
                    emit (.call (some resReg) fnLabel passArgs)
                    if isSvmUnit then
                      let isTailRet := match k with | .return retFid => retFid == decl.fvarId | _ => false
                      if isTailRet then
                        setTerm (.ret resReg)
                        return ()
                      else
                        let okBlk ← newBlock #[]
                        let errBlk ← newBlock #[]
                        setTerm (.brCmpImm .eq resReg 0 okBlk #[] errBlk #[])
                        switchBlock errBlk
                        let envErr := envMap.insert decl.fvarId (.ctorVal 1 #[.reg resReg, .erased])
                        lowerCode k envErr jpMap onReturn fuel
                        switchBlock okBlk
                        let envOk := envMap.insert decl.fvarId (.ctorVal 0 #[.erased, .erased])
                        lowerCode k envOk jpMap onReturn fuel
                        return ()
                    else if isInfallibleSvm then
                      pure (.ctorVal 0 #[.reg resReg, .erased])
                    else
                      pure (.reg resReg)
                  else
                  -- Check if `calleeDecl` is self-recursive (e.g. `LeanSVM.Input.skipAccounts`)
                  let isSelfRec := containsConst calleeBody declName
                  if isSelfRec then
                    -- Lower recursive helper as a tight in-place loop!
                    let mut pRegs : Array VReg := #[]
                    let mut pKinds : Array Bool := #[]
                    let mut initArgs : Array VReg := #[]
                    let mut calleeEnv : Std.HashMap FVarId Val := {}
                    for idx in [0:calleeDecl.params.size] do
                      let p := calleeDecl.params[idx]!
                      let av := argVals.getD idx .erased
                      if isErasedType p.type || (match av with | .erased => true | _ => false) then
                        pKinds := pKinds.push false
                        calleeEnv := calleeEnv.insert p.fvarId .erased
                      else
                        let pr ← freshVReg
                        pRegs := pRegs.push pr
                        pKinds := pKinds.push true
                        initArgs := initArgs.push (← valToReg av)
                        calleeEnv := calleeEnv.insert p.fvarId (.reg pr)
                    let loopBlk ← newBlock pRegs
                    setTerm (.jmp loopBlk initArgs)
                    switchBlock loopBlk
                    -- Push active loop onto stack & lower body; if continuation `k` is trivial `return decl.fvarId`,
                    -- forward directly to `onReturn`! Otherwise ALWAYS join `(tagReg, payReg)` so errors propagate!
                    modify fun st => { st with activeRecLoops := (declName, loopBlk, pRegs, pKinds) :: st.activeRecLoops }
                    let isDirectTailRet := match k with | .return retFid => retFid == decl.fvarId | _ => false
                    if isDirectTailRet then
                      lowerCode calleeBody calleeEnv {} onReturn (fuel - 1)
                      modify fun st => { st with activeRecLoops := st.activeRecLoops.tail! }
                      return ()
                    else
                      -- Loop produces a value consumed by continuation `k` (e.g. `let after ← skipAccounts ...; ...`)
                      let tagReg ← freshVReg
                      let payReg ← freshVReg
                      let afterBlk ← newBlock #[tagReg, payReg]
                      lowerCode calleeBody calleeEnv {} (fun rv => do
                        match rv with
                        | .ctorVal tag fields =>
                          let tReg ← emitConst tag.toUInt64
                          let pReg ← valToReg (fields.getD 0 .erased)
                          setTerm (.jmp afterBlk #[tReg, pReg])
                        | .dynCtor t ps =>
                          let pReg := ps.getD 0 t
                          setTerm (.jmp afterBlk #[t, pReg])
                        | other =>
                          let tReg ← emitConst 0
                          let pReg ← valToReg other
                          setTerm (.jmp afterBlk #[tReg, pReg])) (fuel - 1)
                      modify fun st => { st with activeRecLoops := st.activeRecLoops.tail! }
                      switchBlock afterBlk
                      -- Peel forall binders to inspect actual return type (e.g. `Ptr → UInt64 → SvmState → SvmStep Ptr`)
                      let rec peelForall (e : Expr) : Expr :=
                        match e with
                        | .forallE _ _ b _ => peelForall b
                        | other => other
                      let retTyFn := (peelForall calleeDecl.type).getAppFn.constName?
                      let retVal : Val :=
                        if retTyFn == some ``LeanSVM.SvmStep then
                          .dynCtor tagReg #[payReg]
                        else
                          .reg payReg
                      let envMap' := envMap.insert decl.fvarId retVal
                      lowerCode k envMap' jpMap onReturn (fuel - 1)
                      return ()
                  else
                    -- Non-recursive helper: inline with join-point continuation (prevents O(2^N) code blowup!)
                    let mut calleeEnv : Std.HashMap FVarId Val := {}
                    for idx in [0:calleeDecl.params.size] do
                      let p := calleeDecl.params[idx]!
                      calleeEnv := calleeEnv.insert p.fvarId (argVals.getD idx .erased)
                    let isTailRet := match k with | .return retFid => retFid == decl.fvarId | _ => false
                    if isTailRet then
                      lowerCode calleeBody calleeEnv {} onReturn (fuel - 1)
                      return ()
                    else if isSvmStepScalarOrUnitType calleeDecl.type then
                      -- Join all return paths of `calleeBody` into a single `afterBlk(tagReg, payReg)`
                      -- so continuation `k` is lowered EXACTLY ONCE (O(N) instead of O(2^N))!
                      let tagReg ← freshVReg
                      let payReg ← freshVReg
                      let afterBlk ← newBlock #[tagReg, payReg]
                      lowerCode calleeBody calleeEnv {} (fun rv => do
                        match rv with
                        | .ctorVal tag fields =>
                          let tReg ← emitConst tag.toUInt64
                          let pReg ← valToReg (fields.getD 0 .erased)
                          setTerm (.jmp afterBlk #[tReg, pReg])
                        | .dynCtor t ps =>
                          let pReg := ps.getD 0 t
                          setTerm (.jmp afterBlk #[t, pReg])
                        | other =>
                          let tReg ← emitConst 0
                          let pReg ← valToReg other
                          setTerm (.jmp afterBlk #[tReg, pReg])) (fuel - 1)
                      switchBlock afterBlk
                      let envMap' := envMap.insert decl.fvarId (.dynCtor tagReg #[payReg])
                      lowerCode k envMap' jpMap onReturn fuel
                      return ()
                    else if isScalarType calleeDecl.type && codeSize calleeBody > 4 then
                      let resReg ← freshVReg
                      let afterBlk ← newBlock #[resReg]
                      lowerCode calleeBody calleeEnv {} (fun rv => do
                        let r ← valToReg rv
                        setTerm (.jmp afterBlk #[r])) (fuel - 1)
                      switchBlock afterBlk
                      let envMap' := envMap.insert decl.fvarId (.reg resReg)
                      lowerCode k envMap' jpMap onReturn fuel
                      return ()
                    else
                      -- Compound struct-returning helper (e.g. `Input.parse*`): CPS inline so SROA eliminates struct!
                      lowerCode calleeBody calleeEnv {} (fun rv => do
                        let envMap' := envMap.insert decl.fvarId rv
                        lowerCode k envMap' jpMap onReturn fuel) (fuel - 1)
                      return ()
                | .extern _ =>
                  throw s!"unsupported external Lean declaration in sBPF program: {declName}"
              | none =>
                throw s!"declaration not found in LCNF environment: {declName}"
    let envMap' := envMap.insert decl.fvarId val
    lowerCode k envMap' jpMap onReturn fuel

  | .fun _ _ _ =>
    throw "local closures (`Code.fun`) are not supported in zero-allocation sBPF; mark helpers `@[inline]` or top-level"

  | .jp jpDecl k =>
    -- Lower join point `jpDecl` as a first-class SSA basic block with block parameters!
    let mut pRegs : Array VReg := #[]
    let mut pKinds : Array Bool := #[]
    let mut jpEnv := envMap
    for p in jpDecl.params do
      if isErasedType p.type then
        pKinds := pKinds.push false
        jpEnv := jpEnv.insert p.fvarId .erased
      else
        let pr ← freshVReg
        pRegs := pRegs.push pr
        pKinds := pKinds.push true
        jpEnv := jpEnv.insert p.fvarId (.reg pr)
    let jpBlk ← newBlock pRegs
    let jpMap' := jpMap.insert jpDecl.fvarId { blockId := jpBlk, paramRegs := pRegs, paramKind := pKinds }
    -- Lower `k` first so all incoming `jmp jpBlk args` edges exist before lowering `jpDecl.value`!
    lowerCode k envMap jpMap' onReturn (fuel - 1)
    let savedBlk := (← get).curBlock
    switchBlock jpBlk
    lowerCode jpDecl.value jpEnv jpMap onReturn (fuel - 1)
    switchBlock savedBlk

  | .jmp fid args =>
    match jpMap.get? fid with
    | some jp =>
      let mut jmpRegs : Array VReg := #[]
      for idx in [0:jp.paramKind.size] do
        if jp.paramKind[idx]! then
          let av := lowerArg envMap (args.getD idx .erased)
          jmpRegs := jmpRegs.push (← valToReg av)
      setTerm (.jmp jp.blockId jmpRegs)
    | none => throw s!"undefined join point fvar: {fid.name}"

  | .cases cs =>
    let discrVal := envMap.getD cs.discr .erased
    -- Helper to lower a chosen `Alt .pure` binding its constructor fields
    let lowerAlt (alt : Alt .pure) (fields : Array Val) : LowerM Unit := do
      match alt with
      | .alt _ params body _ =>
        let mut e := envMap
        for idx in [0:params.size] do
          e := e.insert params[idx]!.fvarId (fields.getD idx .erased)
        lowerCode body e jpMap onReturn (fuel - 1)
      | .default body =>
        lowerCode body envMap jpMap onReturn (fuel - 1)
      | .ctorAlt _ body _ =>
        lowerCode body envMap jpMap onReturn (fuel - 1)

    match discrVal with
    -- Case 1: Compile-time known constructor (ZERO instructions emitted! Folded completely!)
    | .ctorVal knownTag fields =>
      let matched? := cs.alts.find? fun alt =>
        match alt with
        | .alt ctorName _ _ _ => getCtorIdx env ctorName == knownTag
        | .default _ => false
        | .ctorAlt info _ _ => info.cidx == knownTag
      match matched? with
      | some alt => lowerAlt alt fields
      | none =>
        match cs.alts.find? (fun a => match a with | .default _ => true | _ => false) with
        | some dflt => lowerAlt dflt #[]
        | none => setTerm .unreach

    -- Case 2: Compile-time known 1-constructor struct (ZERO instructions!)
    | .structVal fields =>
      if cs.alts.size > 0 then lowerAlt cs.alts[0]! fields
      else setTerm .unreach

    -- Case 3: Dynamic tagged constructor (e.g. `SvmStep` returned from a loop!)
    | .dynCtor tagReg payloads =>
      let fields := payloads.map Val.reg
      lowerSwitch tagReg fields cs.alts envMap jpMap onReturn (fuel - 1)

    -- Case 4: Dynamic scalar (`Bool`, `UInt8/64`, enum tag)
    | .reg tagReg =>
      lowerSwitch tagReg #[] cs.alts envMap jpMap onReturn (fuel - 1)

    | .natLit n =>
      let r ← emitConst n.toUInt64
      lowerSwitch r #[] cs.alts envMap jpMap onReturn (fuel - 1)

    | .erased =>
      if cs.alts.size > 0 then lowerAlt cs.alts[0]! #[]
      else setTerm .unreach

    | other => throw s!"cannot branch on value: {repr other}"

where
  containsConst (c : Code .pure) (target : Name) : Bool :=
    match c with
    | .let d k =>
      let hit := match d.value with | .const n _ _ _ => n == target | _ => false
      hit || containsConst k target
    | .jp d k => containsConst d.value target || containsConst k target
    | .fun d k _ => containsConst d.value target || containsConst k target
    | .cases cs => cs.alts.any fun a =>
      match a with
      | .alt _ _ body _ | .default body | .ctorAlt _ body _ => containsConst body target
    | _ => false

  extractLoopVal (v : Val) : LowerM VReg :=
    match v with
    | .ctorVal _ fields => valToReg (fields.getD 0 .erased)
    | .dynCtor _ ps => return ps.getD 0 0
    | other => valToReg other

  lowerSwitch (tagReg : VReg) (fields : Array Val) (alts : Array (Alt .pure))
      (envMap : Std.HashMap FVarId Val) (jpMap : Std.HashMap FVarId JpInfo)
      (onReturn : Val → LowerM Unit) (fuel : Nat) : LowerM Unit := do
    let env := (← get).env
    -- Separate explicit constructor alternatives from optional default
    let mut explicit : Array (Nat × Alt .pure) := #[]
    let mut default? : Option (Alt .pure) := none
    for a in alts do
      match a with
      | .alt ctorName _ _ _ => explicit := explicit.push (getCtorIdx env ctorName, a)
      | .ctorAlt info _ _   => explicit := explicit.push (info.cidx, a)
      | .default _          => default? := some a

    let lowerOne (alt : Alt .pure) : LowerM Unit :=
      match alt with
      | .alt _ params body _ =>
        let e := Id.run do
          let mut m := envMap
          for idx in [0:params.size] do
            m := m.insert params[idx]!.fvarId (fields.getD idx .erased)
          return m
        lowerCode body e jpMap onReturn fuel
      | .default body | .ctorAlt _ body _ =>
        lowerCode body envMap jpMap onReturn fuel

    if explicit.isEmpty then
      match default? with
      | some d => lowerOne d
      | none => setTerm .unreach
    else if explicit.size == 1 && default?.isNone then
      lowerOne explicit[0]!.2
    else if explicit.size == 2 && default?.isNone then
      -- Fast 2-way branch (e.g., `Bool` or `SvmStep`) with scoped stack high-water-mark reuse!
      let (tag0, alt0) := explicit[0]!
      let (_, alt1) := explicit[1]!
      let savedStack := (← get).stackAllocBytes
      let savedRetSlot := (← get).callRetSlotOff?
      let savedArgsPack := (← get).callArgsPack?
      let blk0 ← newBlock
      let blk1 ← newBlock
      setTerm (.brCmpImm .eq tagReg (Int32.ofInt tag0) blk0 #[] blk1 #[])
      switchBlock blk0
      lowerOne alt0
      let stack0 := (← get).stackAllocBytes
      modify fun st => { st with stackAllocBytes := savedStack, callRetSlotOff? := savedRetSlot, callArgsPack? := savedArgsPack }
      switchBlock blk1
      lowerOne alt1
      let stack1 := (← get).stackAllocBytes
      modify fun st => { st with stackAllocBytes := max stack0 stack1, callRetSlotOff? := savedRetSlot, callArgsPack? := savedArgsPack }
    else
      -- Multi-way switch chain with scoped stack reuse across mutually exclusive arms!
      let savedStack := (← get).stackAllocBytes
      let savedRetSlot := (← get).callRetSlotOff?
      let savedArgsPack := (← get).callArgsPack?
      let mut maxStack := savedStack
      let mut curIdx := 0
      while curIdx < explicit.size do
        let (tagI, altI) := explicit[curIdx]!
        let isLast := curIdx + 1 == explicit.size && default?.isNone
        if isLast then
          modify fun st => { st with stackAllocBytes := savedStack, callRetSlotOff? := savedRetSlot, callArgsPack? := savedArgsPack }
          lowerOne altI
          maxStack := max maxStack (← get).stackAllocBytes
        else
          let hitBlk ← newBlock
          let nextBlk ← newBlock
          setTerm (.brCmpImm .eq tagReg (Int32.ofInt tagI) hitBlk #[] nextBlk #[])
          switchBlock hitBlk
          modify fun st => { st with stackAllocBytes := savedStack, callRetSlotOff? := savedRetSlot, callArgsPack? := savedArgsPack }
          lowerOne altI
          maxStack := max maxStack (← get).stackAllocBytes
          switchBlock nextBlk
        curIdx := curIdx + 1
      if let some d := default? then
        modify fun st => { st with stackAllocBytes := savedStack, callRetSlotOff? := savedRetSlot, callArgsPack? := savedArgsPack }
        lowerOne d
        maxStack := max maxStack (← get).stackAllocBytes
      modify fun st => { st with stackAllocBytes := maxStack, callRetSlotOff? := savedRetSlot, callArgsPack? := savedArgsPack }

/-- Lower a top-level Lean 4 Solana entrypoint declaration (`input : Ptr → SolanaM Unit` or `Ptr → UInt64`)
    from its monomorphic LCNF into an unoptimized `SbfIR.Program`. -/
def lowerEntrypoint (env : Environment) (entryName : Name) : Except String Program := do
  let some decl := lookupDecl? env entryName
    | throw s!"entrypoint declaration '{entryName}' not found in LCNF environment (ensure module is built and imported)"
  let body ← match decl.value with
    | .code c => pure c
    | .extern _ => throw s!"entrypoint '{entryName}' is extern and has no Lean body"

  let action : LowerM Func := do
    let entryBlk ← newBlock #[]
    switchBlock entryBlk
    -- Bind entrypoint parameters: param 0 is `input : Ptr` (in sBPF `r1`), param 1 (if `SolanaM`) is erased `SvmState`!
    let mut envMap : Std.HashMap FVarId Val := {}
    let mut irParams : Array VReg := #[]
    for idx in [0:decl.params.size] do
      let p := decl.params[idx]!
      if idx == 0 && !isErasedType p.type then
        let r ← freshVReg
        irParams := irParams.push r
        envMap := envMap.insert p.fvarId (.reg r)
      else if isErasedType p.type then
        envMap := envMap.insert p.fvarId .erased
      else
        throw s!"Solana entrypoint '{entryName}' has unexpected extra parameter '{p.binderName}' (expected `(input : Ptr) : SolanaM Unit` or `(input : Ptr) : UInt64`)"
    lowerCode body envMap {} lowerEntryReturn 100000
    let st ← get
    return {
      name := entryName.toString
      params := irParams
      blocks := st.blocks
      stackAllocBytes := st.stackAllocBytes
      nextVReg := st.nextVReg
    }

  let (counts, _) := countCodeCalls env body {} {} 16
  let initState : LowerState := { env, callCounts := counts }
  match action.run initState with
  | .ok (fn, finalSt) =>
    return { entry := fn, helpers := finalSt.outlinedHelpers, rodata := finalSt.rodata.bytes }
  | .error e => .error e

end LeanSVM.Compiler
