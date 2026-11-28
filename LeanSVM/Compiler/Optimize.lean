/-
  LeanSVM.Compiler.Optimize
  High-impact SSA IR optimizer for Solana sBPF (designed to rival/beat hand-rolled sBPF):
  1. Copy propagation & constant block-parameter propagation
  2. Constant folding & power-of-2 strength reduction (`mul/div/mod` -> `lsh/rsh/and`)
  3. Immediate operand folding (`binOp` -> `binImm`, `store` -> `storeImm`)
  4. Address-offset folding (`v = base + k; load/store [v + off]` -> `load/store [base + (k + off)]`)
  5. Direct `r10` stack folding (`v = r10 + sOff; load/store [v + off]` -> `loadStack/storeStack/storeStackImm`)
  6. Compare-and-branch fusion & operand flipping (`1 <= r` -> `r >= 1`)
  7. Unsigned interval range analysis (`VRange = [lo, hi]`): safe `add32`/`sub32`/`mul32` -> `alu64`
     promotion, redundant low-bit mask elimination (`x & (2^k - 1)` -> `x`), and range-proven branch folding
  8. Small constant-length `sol_memset_` inline expansion (`<= 5` stores, `<= 40 B`)
  9. Local CSE (deduplicates repeated pure ALU/address computations within blocks)
  10. Dead Code & Dead Block-Parameter Elimination (DCE) + Interprocedural Dead Helper Elimination
  11. Tail Merging (deduplicates identical error-exit blocks -> slashes `.so` binary size!)
  12. Unreachable block & forwarding-trampoline pruning + `O(log N)` binary-search switch dispatch
-/
import LeanSVM.Compiler.IR
import LeanSVM.SBPF.Peephole
import Std.Data.HashMap
import Std.Data.HashSet

namespace LeanSVM.Compiler

/-! ### Sound Unsigned 64-Bit Interval Range Lattice (`VRange`) -/

/-- Sound unsigned 64-bit interval `[lo, hi]` representing all `v : UInt64` with
    `lo ≤ v.toNat ≤ hi`. Unconstrained values use `VRange.top = [0, 2^64 - 1]`. -/
structure VRange where
  lo : Nat
  hi : Nat
  deriving Repr, BEq, Inhabited

namespace VRange

def u64Max : Nat := 0xFFFFFFFFFFFFFFFF
def u32Max : Nat := 0xFFFFFFFF
def s64Max : Nat := 0x7FFFFFFFFFFFFFFF

def top  : VRange := ⟨0, u64Max⟩
def u8   : VRange := ⟨0, 0xFF⟩
def u16  : VRange := ⟨0, 0xFFFF⟩
def u32  : VRange := ⟨0, u32Max⟩
def bool : VRange := ⟨0, 1⟩

def exact (v : UInt64) : VRange := ⟨v.toNat, v.toNat⟩

def contains (r : VRange) (v : UInt64) : Prop :=
  r.lo ≤ v.toNat ∧ v.toNat ≤ r.hi

def join (a b : VRange) : VRange :=
  ⟨min a.lo b.lo, max a.hi b.hi⟩

def forMemSize : SBPF.MemSize → VRange
  | .b1 => u8
  | .b2 => u16
  | .b4 => u32
  | .b8 => top

/-- Sound abstract transfer function for IR binary operations. -/
def evalBinOp (op : BinOp) (ra rb : VRange) : VRange :=
  match op with
  | .add64 =>
    if ra.hi + rb.hi ≤ u64Max then ⟨ra.lo + rb.lo, ra.hi + rb.hi⟩ else top
  | .sub64 =>
    if rb.hi ≤ ra.lo then ⟨ra.lo - rb.hi, ra.hi - rb.lo⟩ else top
  | .mul64 =>
    if ra.hi * rb.hi ≤ u64Max then ⟨ra.lo * rb.lo, ra.hi * rb.hi⟩ else top
  | .div64 =>
    if rb.lo > 0 then ⟨ra.lo / rb.hi, ra.hi / rb.lo⟩ else ⟨0, ra.hi⟩
  | .mod64 =>
    if rb.hi > 0 then ⟨0, min ra.hi (rb.hi - 1)⟩ else ⟨0, 0⟩
  | .and64 =>
    ⟨0, min ra.hi rb.hi⟩
  | .or64 | .xor64 =>
    if ra.hi ≤ 0xFF && rb.hi ≤ 0xFF then u8
    else if ra.hi ≤ 0xFFFF && rb.hi ≤ 0xFFFF then u16
    else if ra.hi ≤ u32Max && rb.hi ≤ u32Max then u32
    else top
  | .rsh64 =>
    if rb.hi < 64 then ⟨ra.lo >>> rb.hi, ra.hi >>> rb.lo⟩ else ⟨0, ra.hi⟩
  | .lsh64 =>
    if rb.hi < 64 && ra.hi * (2 ^ rb.hi) ≤ u64Max then
      ⟨ra.lo * (2 ^ rb.lo), ra.hi * (2 ^ rb.hi)⟩
    else top
  | .arsh64 => top
  | .add32 =>
    if ra.hi + rb.hi ≤ u32Max then ⟨ra.lo + rb.lo, ra.hi + rb.hi⟩ else u32
  | .sub32 =>
    if ra.hi ≤ u32Max && rb.hi ≤ ra.lo then ⟨ra.lo - rb.hi, ra.hi - rb.lo⟩ else u32
  | .mul32 =>
    if ra.hi * rb.hi ≤ u32Max then ⟨ra.lo * rb.lo, ra.hi * rb.hi⟩ else u32
  | .and32 =>
    ⟨0, min (min ra.hi rb.hi) u32Max⟩
  | .div32 | .mod32 | .or32 | .xor32 | .lsh32 | .rsh32 => u32

/-- Sound abstract transfer function for IR immediate binary operations. -/
def evalBinImm (op : BinOp) (ra : VRange) (imm : Int32) : VRange :=
  let rb := exact (if op.is32 then (Int32.toUInt32 imm).toUInt64
                   else Int64.toUInt64 (Int64.ofInt imm.toInt))
  evalBinOp op ra rb

/-- Returns `some true` / `some false` when intervals `ra`, `rb` statically decide `op`. -/
def evalCmp? (op : CmpOp) (ra rb : VRange) : Option Bool :=
  match op with
  | .eq =>
    if ra.hi < rb.lo || rb.hi < ra.lo then some false
    else if ra.lo == ra.hi && rb.lo == rb.hi && ra.lo == rb.lo then some true
    else none
  | .ne =>
    if ra.hi < rb.lo || rb.hi < ra.lo then some true
    else if ra.lo == ra.hi && rb.lo == rb.hi && ra.lo == rb.lo then some false
    else none
  | .ult =>
    if ra.hi < rb.lo then some true
    else if rb.hi ≤ ra.lo then some false
    else none
  | .ule =>
    if ra.hi ≤ rb.lo then some true
    else if rb.hi < ra.lo then some false
    else none
  | .ugt =>
    if rb.hi < ra.lo then some true
    else if ra.hi ≤ rb.lo then some false
    else none
  | .uge =>
    if rb.hi ≤ ra.lo then some true
    else if ra.hi < rb.lo then some false
    else none
  | .slt =>
    if ra.hi ≤ s64Max && rb.hi ≤ s64Max then
      if ra.hi < rb.lo then some true
      else if rb.hi ≤ ra.lo then some false
      else none
    else none
  | .sle =>
    if ra.hi ≤ s64Max && rb.hi ≤ s64Max then
      if ra.hi ≤ rb.lo then some true
      else if rb.hi < ra.lo then some false
      else none
    else none
  | .sgt =>
    if ra.hi ≤ s64Max && rb.hi ≤ s64Max then
      if rb.hi < ra.lo then some true
      else if ra.hi ≤ rb.lo then some false
      else none
    else none
  | .sge =>
    if ra.hi ≤ s64Max && rb.hi ≤ s64Max then
      if rb.hi ≤ ra.lo then some true
      else if ra.hi < rb.lo then some false
      else none
    else none

/-- True iff `m = 2^k - 1` for some `k ∈ [1..64]` (`0x1`, `0xFF`, `0xFFFF`, `0xFFFFFFFF`, ...). -/
def isLowBitMask (m : UInt64) : Bool :=
  m != 0 && (m &&& (m + 1)) == 0

/-- Safely promote a sign-extending sBPF `ALU32` op (`add32`/`sub32`/`mul32`) to its
    exact 64-bit equivalent whenever operand ranges guarantee zero 32-bit wraparound.
    Eliminates the trailing `mov32 rd, rd` fixup AND unlocks 64-bit constant/address folding! -/
def canPromoteAlu32 (op : BinOp) (ra rb : VRange) : Option BinOp :=
  match op with
  | .add32 => if ra.hi + rb.hi ≤ u32Max then some .add64 else none
  | .sub32 => if ra.hi ≤ u32Max && rb.hi ≤ ra.lo then some .sub64 else none
  | .mul32 => if ra.hi * rb.hi ≤ u32Max then some .mul64 else none
  | _ => none

end VRange

/-! ### Small Constant-Length `sol_memset_` Inline Expansion (`<= 5` stores) -/

/-- Plan a sequence of `<= maxStores` immediate stores (`(MemSize, offset, imm32)`) that
    writes `byte` to every byte in `[base, base + len)`, or `none` if `len` exceeds the budget.
    Uses 8-byte `storeImm .b8` (`0` or `-1`) for `0x00`/`0xFF` (up to 40 bytes in 5 stores)
    and 4-byte `storeImm .b4` for arbitrary constant bytes (up to 20 bytes in 5 stores). -/
def planMemsetStores (byte : UInt8) (len : Nat) (maxStores : Nat := 5) :
    Option (List (SBPF.MemSize × Int16 × Int32)) :=
  if len > 40 then none
  else
    let rec go (rem off : Nat) (fuel : Nat) : Option (List (SBPF.MemSize × Int16 × Int32)) :=
      if rem == 0 then some []
      else match fuel with
        | 0 => none
        | fuel' + 1 =>
          let bNat := byte.toNat
          if rem >= 8 && (byte == 0 || byte == 0xFF) then
            let imm : Int32 := if byte == 0 then 0 else -1
            (go (rem - 8) (off + 8) fuel').map ((.b8, Int16.ofInt off, imm) :: ·)
          else if rem >= 4 then
            let w32 : UInt32 := (bNat + bNat * 256 + bNat * 65536 + bNat * 16777216).toUInt32
            (go (rem - 4) (off + 4) fuel').map ((.b4, Int16.ofInt off, UInt32.toInt32 w32) :: ·)
          else if rem >= 2 then
            let w16 : Int := (bNat + bNat * 256 : Nat)
            (go (rem - 2) (off + 2) fuel').map ((.b2, Int16.ofInt off, Int32.ofInt w16) :: ·)
          else
            (go (rem - 1) (off + 1) fuel').map ((.b1, Int16.ofInt off, Int32.ofInt bNat) :: ·)
    go len 0 maxStores

def log2IfPow2 (v : UInt64) : Option Nat :=
  if v == 0 || (v &&& (v - 1)) != 0 then none
  else
    let rec go (x : UInt64) (k : Nat) (fuel : Nat) : Nat :=
      match fuel with
      | 0 => k
      | n + 1 => if x <= 1 then k else go (x >>> 1) (k + 1) n
    some (go v 0 64)

private def memSizeTag : SBPF.MemSize → Nat
  | .b1 => 0 | .b2 => 1 | .b4 => 2 | .b8 => 3

private def fitsInt16 (x : Int) : Option Int16 :=
  if x >= -32768 && x <= 32767 then some (Int16.ofInt x) else none

private def fitsInt32Int (x : Int) : Option Int32 :=
  if x >= -2147483648 && x <= 2147483647 then some (Int32.ofInt x) else none

private def fitsInt32U64 (v : UInt64) : Option Int32 :=
  SBPF.fitsInt32 v

private def resolveAlias (aliasMap : Std.HashMap VReg VReg) (v : VReg) : VReg := Id.run do
  let mut cur := v
  for _ in [0:16] do
    match aliasMap.get? cur with
    | some nxt => if nxt == cur then break else cur := nxt
    | none => break
  return cur

/-- Substitute register aliases in a statement. -/
private def substStmt (am : Std.HashMap VReg VReg) : Stmt → Stmt
  | .mov d s               => .mov d (resolveAlias am s)
  | .binOp op d l r        => .binOp op d (resolveAlias am l) (resolveAlias am r)
  | .binImm op d l imm     => .binImm op d (resolveAlias am l) imm
  | .neg64 d s             => .neg64 d (resolveAlias am s)
  | .cmp op d l r          => .cmp op d (resolveAlias am l) (resolveAlias am r)
  | .load sz d b off       => .load sz d (resolveAlias am b) off
  | .store sz b off v      => .store sz (resolveAlias am b) off (resolveAlias am v)
  | .storeImm sz b off imm => .storeImm sz (resolveAlias am b) off imm
  | .storeStack sz off v   => .storeStack sz off (resolveAlias am v)
  | .syscall d? s args     => .syscall d? s (args.map (resolveAlias am))
  | .call d? s args        => .call d? s (args.map (resolveAlias am))
  | s                      => s

/-- Substitute register aliases in a terminator. -/
private def substTerm (am : Std.HashMap VReg VReg) : Term → Term
  | .jmp t a                     => .jmp t (a.map (resolveAlias am))
  | .br c t ta e ea              => .br (resolveAlias am c) t (ta.map (resolveAlias am)) e (ea.map (resolveAlias am))
  | .brCmp op l r t ta e ea      => .brCmp op (resolveAlias am l) (resolveAlias am r) t (ta.map (resolveAlias am)) e (ea.map (resolveAlias am))
  | .brCmpImm op l imm t ta e ea => .brCmpImm op (resolveAlias am l) imm t (ta.map (resolveAlias am)) e (ea.map (resolveAlias am))
  | .ret v                       => .ret (resolveAlias am v)
  | .unreach                     => .unreach

/-- Forward pass: copy propagation, constant folding, strength reduction, address-offset &
    direct `r10` stack folding, `storeImm` folding, local CSE, and compare-branch fusion. -/
private def forwardOptPass (f : Func) : Func × Bool := Id.run do
  let mut consts    : Std.HashMap VReg UInt64 := {}
  let mut aliases   : Std.HashMap VReg VReg := {}
  let mut addOffs   : Std.HashMap VReg (VReg × Int) := {} -- v = base + offset
  let mut stackOffs : Std.HashMap VReg Int := {}          -- v = r10 + offset
  let mut cmpDefs   : Std.HashMap VReg (CmpOp × VReg × VReg) := {}
  let mut ranges    : Std.HashMap VReg VRange := {}
  let mut changed   := false

  -- Pre-scan `constImm` and record incoming edges (with predecessor index in `f.blocks`)
  let mut incomingArgs : Std.HashMap BlockId (Array (Nat × Array VReg)) := {}
  let addIncoming (m : Std.HashMap BlockId (Array (Nat × Array VReg)))
      (predIdx : Nat) (tgt : BlockId) (args : Array VReg) :=
    if args.isEmpty then m else m.insert tgt ((m.getD tgt #[]).push (predIdx, args))
  for bi in [0:f.blocks.size] do
    let blk := f.blocks[bi]!
    for s in blk.stmts do
      match s with
      | .constImm d v => consts := consts.insert d v
      | _ => pure ()
    match blk.term with
    | .jmp t a => incomingArgs := addIncoming incomingArgs bi t a
    | .br _ t ta e ea | .brCmp _ _ _ t ta e ea | .brCmpImm _ _ _ t ta e ea =>
      incomingArgs := addIncoming (addIncoming incomingArgs bi t ta) bi e ea
    | _ => pure ()

  for blk in f.blocks do
    if blk.id != 0 && !blk.params.isEmpty then
      if let some edges := incomingArgs.get? blk.id then
        if !edges.isEmpty then
          for k in [0:blk.params.size] do
            let p := blk.params[k]!
            let mut commonC? : Option UInt64 := none
            let mut allSameC := true
            let mut commonV? : Option VReg := none
            let mut allSameV := true
            for (_, edge) in edges do
              if k < edge.size then
                let arg := edge[k]!
                -- Constant propagation across incoming edges (ignoring self-loops `arg == p`)
                if arg != p then
                  match consts.get? arg with
                  | some cv =>
                    match commonC? with
                    | none => commonC? := some cv
                    | some prev => if prev != cv then allSameC := false
                  | none => allSameC := false
                  match commonV? with
                  | none => commonV? := some arg
                  | some prev => if prev != arg then allSameV := false
              else
                allSameC := false
                allSameV := false
            if allSameV then
              if let some v := commonV? then
                aliases := aliases.insert p v
                changed := true
            if allSameC then
              if let some cv := commonC? then
                consts := consts.insert p cv

  let mut newBlocks : Array Block := Array.emptyWithCapacity f.blocks.size

  for bi in [0:f.blocks.size] do
    let blk := f.blocks[bi]!
    -- Sound acyclic merge for block-parameter ranges: ONLY refine when EVERY incoming edge
    -- originates from a strictly earlier block (`predIdx < bi`), keeping loop headers safely at `top`.
    if blk.id != 0 && !blk.params.isEmpty then
      if let some edges := incomingArgs.get? blk.id then
        if !edges.isEmpty && edges.all (fun e => e.1 < bi) then
          for k in [0:blk.params.size] do
            let p := blk.params[k]!
            let mut joined? : Option VRange := none
            let mut ok := true
            for (_, edge) in edges do
              if k < edge.size then
                let arg := resolveAlias aliases edge[k]!
                let rArg := match consts.get? arg with
                  | some c => VRange.exact c
                  | none => ranges.getD arg VRange.top
                joined? := match joined? with
                  | none => some rArg
                  | some prev => some (VRange.join prev rArg)
              else
                ok := false
            if ok then
              if let some jr := joined? then
                ranges := ranges.insert p jr

    let mut outStmts : Array Stmt := Array.emptyWithCapacity blk.stmts.size
    -- Local CSE table within the current basic block: `(opTag, lhs, rhsOrImm) -> vreg`
    let mut localBinImmCse : Std.HashMap (Nat × VReg × Int) VReg := {}
    -- Local load-CSE & store-to-load forwarding (conservatively invalidated on stores/calls/syscalls)
    let mut localLoads      : Std.HashMap (VReg × Int × Nat) VReg := {}
    let mut localStackLoads : Std.HashMap (Int × Nat) VReg := {}
    for rawStmt in blk.stmts do
      let s0 := substStmt aliases rawStmt
      if s0 != rawStmt then changed := true

      let getRange (v : VReg) : VRange :=
        match consts.get? v with
        | some c => VRange.exact c
        | none => ranges.getD v VRange.top

      let mut s1 : Stmt := s0
      let mut keepStmt : Bool := true
      match s0 with
      | .constImm d v =>
        consts := consts.insert d v
        ranges := ranges.insert d (VRange.exact v)
      | .stackAddr d sOff =>
        stackOffs := stackOffs.insert d sOff.toInt
      | .mov d src =>
        if d != src then
          aliases := aliases.insert d src
          if let some c := consts.get? src then consts := consts.insert d c
          if let some r := ranges.get? src then ranges := ranges.insert d r
          if let some ao := addOffs.get? src then addOffs := addOffs.insert d ao
          if let some so := stackOffs.get? src then stackOffs := stackOffs.insert d so
      | .binOp op0 d l r =>
        let rl := getRange l
        let rr := getRange r
        let (op, promoted) :=
          match VRange.canPromoteAlu32 op0 rl rr with
          | some op64 => (op64, true)
          | none => (op0, false)
        if promoted then
          changed := true
          s1 := .binOp op d l r
        ranges := ranges.insert d (VRange.evalBinOp op rl rr)
        match consts.get? l, consts.get? r with
        | some cl, some cr =>
          if let some cv := op.evalConst cl cr then
            changed := true
            consts := consts.insert d cv
            ranges := ranges.insert d (VRange.exact cv)
            s1 := .constImm d cv
        | _, some cr =>
          match op with
          | .add64 =>
            if cr == 0 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some so := stackOffs.get? l then
              if let some i32 := fitsInt32U64 cr then
                let total := so + i32.toInt
                if let some s16 := fitsInt16 total then
                  changed := true
                  stackOffs := stackOffs.insert d total
                  s1 := .stackAddr d s16
            else
              match addOffs.get? l, fitsInt32U64 cr with
              | some (base, off1), some i32 =>
                let total := off1 + i32.toInt
                match fitsInt32Int total with
                | some tot32 =>
                  changed := true
                  addOffs := addOffs.insert d (base, total)
                  s1 := .binImm .add64 d base tot32
                | none =>
                  changed := true
                  addOffs := addOffs.insert d (l, i32.toInt)
                  s1 := .binImm .add64 d l i32
              | none, some i32 =>
                changed := true
                addOffs := addOffs.insert d (l, i32.toInt)
                s1 := .binImm .add64 d l i32
              | _, none => pure ()
          | .sub64 =>
            if cr == 0 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some i32 := fitsInt32U64 cr then
              -- Normalize `sub64 d, l, imm` to `add64 d, l, (-imm)` when `-imm` fits in Int32:
              -- avoids sBPF v3's reversed `SUB64_IMM` (`imm - dst`, SIMD-0174) and unlocks CSE/folding.
              if let some negI32 := fitsInt32Int (-i32.toInt) then
                changed := true
                addOffs := addOffs.insert d (l, negI32.toInt)
                s1 := .binImm .add64 d l negI32
          | .mul64 =>
            if cr == 0 then
              changed := true; consts := consts.insert d 0; ranges := ranges.insert d (VRange.exact 0); s1 := .constImm d 0
            else if cr == 1 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else
              match log2IfPow2 cr with
              | some k => changed := true; s1 := .binImm .lsh64 d l (Int32.ofInt k)
              | none =>
                if let some i32 := fitsInt32U64 cr then
                  changed := true; s1 := .binImm .mul64 d l i32
          | .div64 =>
            if cr == 1 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else
              match log2IfPow2 cr with
              | some k => changed := true; s1 := .binImm .rsh64 d l (Int32.ofInt k)
              | none =>
                if cr > 0 && cr <= 0x7FFFFFFF then
                  changed := true; s1 := .binImm .div64 d l (Int32.ofInt cr.toNat)
          | .mod64 =>
            if cr == 1 then
              changed := true; consts := consts.insert d 0; ranges := ranges.insert d (VRange.exact 0); s1 := .constImm d 0
            else
              match log2IfPow2 cr with
              | some _ =>
                if let some mask32 := fitsInt32U64 (cr - 1) then
                  changed := true; s1 := .binImm .and64 d l mask32
              | none =>
                if cr > 0 && cr <= 0x7FFFFFFF then
                  changed := true; s1 := .binImm .mod64 d l (Int32.ofInt cr.toNat)
          | .or64 =>
            if cr == 0 then changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some i32 := fitsInt32U64 cr then changed := true; s1 := .binImm .or64 d l i32
          | .xor64 =>
            if cr == 0 then changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some i32 := fitsInt32U64 cr then changed := true; s1 := .binImm .xor64 d l i32
          | .and64 =>
            if cr == 0 then changed := true; consts := consts.insert d 0; ranges := ranges.insert d (VRange.exact 0); s1 := .constImm d 0
            else if cr == 0xFFFFFFFFFFFFFFFF || (VRange.isLowBitMask cr && rl.hi <= cr.toNat) then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some i32 := fitsInt32U64 cr then changed := true; s1 := .binImm .and64 d l i32
          | .and32 =>
            let cr32 : UInt64 := cr.toUInt32.toUInt64
            if cr32 == 0 then changed := true; consts := consts.insert d 0; ranges := ranges.insert d (VRange.exact 0); s1 := .constImm d 0
            else if VRange.isLowBitMask cr32 && rl.hi <= cr32.toNat then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some i32 := fitsInt32U64 cr then changed := true; s1 := .binImm .and32 d l i32
          | .lsh64 | .rsh64 | .arsh64 =>
            if (cr &&& 63) == 0 then changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else changed := true; s1 := .binImm op d l (Int32.ofInt (cr &&& 63).toNat)
          | .lsh32 | .rsh32 =>
            -- Mask 32-bit shift immediates into `[0, 31]` (Agave verifier rejects shift imm >= 32!).
            let sh := (cr.toUInt32 &&& 31).toNat
            changed := true
            s1 := .binImm op d l (Int32.ofInt sh)
          | .sub32 =>
            if let some i32 := fitsInt32U64 cr then
              if let some negI32 := fitsInt32Int (-i32.toInt) then
                changed := true; s1 := .binImm .add32 d l negI32
          | .div32 | .mod32 =>
            if cr > 0 && cr <= 0x7FFFFFFF then
              changed := true; s1 := .binImm op d l (Int32.ofInt cr.toNat)
          | _ =>
            if let some i32 := fitsInt32U64 cr then changed := true; s1 := .binImm op d l i32
        | some _, none =>
          if op.isCommutative then
            changed := true
            s1 := .binOp op d r l
        | none, none =>
          if (op == .sub64 || op == .xor64 || op == .sub32 || op == .xor32) && l == r then
            changed := true; consts := consts.insert d 0; ranges := ranges.insert d (VRange.exact 0); s1 := .constImm d 0
      | .binImm op0 d l imm0 =>
        let rl := getRange l
        let imm := op0.maskShiftImm imm0
        if imm != imm0 then
          changed := true
          s1 := .binImm op0 d l imm
        -- Normalize `sub64`/`sub32` immediate to `add64`/`add32` with negated immediate (sBPF v3 SIMD-0174 safe)
        let (op1, imm1) :=
          if op0 == .sub64 then
            match fitsInt32Int (-imm.toInt) with
            | some negI => (.add64, negI)
            | none => (op0, imm)
          else if op0 == .sub32 then
            match fitsInt32Int (-imm.toInt) with
            | some negI => (.add32, negI)
            | none => (op0, imm)
          else (op0, imm)
        if op1 != op0 || imm1 != imm then
          changed := true
          s1 := .binImm op1 d l imm1
        -- Safe `ALU32` immediate promotion requires `imm1.toInt >= 0` so `signExt32 imm1 == zeroExt32 imm1`!
        let (op, promoted) :=
          if imm1.toInt >= 0 then
            let rb := VRange.exact (Int32.toUInt32 imm1).toUInt64
            match VRange.canPromoteAlu32 op1 rl rb with
            | some op64 => (op64, true)
            | none => (op1, false)
          else (op1, false)
        let imm := imm1
        if promoted then
          changed := true
          s1 := .binImm op d l imm
        ranges := ranges.insert d (VRange.evalBinImm op rl imm)
        match consts.get? l with
        | some cl =>
          let cr : UInt64 := if op.is32 then (Int32.toUInt32 imm).toUInt64
                             else Int64.toUInt64 (Int64.ofInt imm.toInt)
          if let some cv := op.evalConst cl cr then
            changed := true
            consts := consts.insert d cv
            ranges := ranges.insert d (VRange.exact cv)
            s1 := .constImm d cv
        | none =>
          if op == .and64 then
            let mask : UInt64 := Int64.toUInt64 (Int64.ofInt imm.toInt)
            if VRange.isLowBitMask mask && rl.hi <= mask.toNat then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
          else if op == .and32 then
            let mask : UInt64 := (Int32.toUInt32 imm).toUInt64
            if VRange.isLowBitMask mask && rl.hi <= mask.toNat then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
          else if op == .add64 then
            if imm == 0 then
              changed := true; aliases := aliases.insert d l; s1 := .mov d l
            else if let some so := stackOffs.get? l then
              let total := so + imm.toInt
              if let some s16 := fitsInt16 total then
                changed := true
                stackOffs := stackOffs.insert d total
                s1 := .stackAddr d s16
            else
              match addOffs.get? l with
              | some (base, off1) =>
                let total := off1 + imm.toInt
                match fitsInt32Int total with
                | some tot32 =>
                  changed := true
                  addOffs := addOffs.insert d (base, total)
                  s1 := .binImm .add64 d base tot32
                | none =>
                  addOffs := addOffs.insert d (l, imm.toInt)
              | none =>
                addOffs := addOffs.insert d (l, imm.toInt)
          -- Local CSE on `binImm .add64` (eliminates duplicate `acc + 8`, `acc + 88`!)
          if op == .add64 then
            match s1 with
            | .binImm .add64 d2 base2 imm2 =>
              let key : Nat × VReg × Int := (0, base2, imm2.toInt)
              match localBinImmCse.get? key with
              | some prev =>
                changed := true
                aliases := aliases.insert d2 prev
                s1 := .mov d2 prev
              | none =>
                localBinImmCse := localBinImmCse.insert key d2
            | _ => pure ()
      | .cmp op d l r =>
        ranges := ranges.insert d VRange.bool
        match consts.get? l, consts.get? r with
        | some cl, some cr =>
          let cv : UInt64 := if op.evalU64 cl cr then 1 else 0
          changed := true
          consts := consts.insert d cv
          ranges := ranges.insert d (VRange.exact cv)
          s1 := .constImm d cv
        | _, _ =>
          match VRange.evalCmp? op (getRange l) (getRange r) with
          | some b =>
            let cv : UInt64 := if b then 1 else 0
            changed := true
            consts := consts.insert d cv
            ranges := ranges.insert d (VRange.exact cv)
            s1 := .constImm d cv
          | none =>
            cmpDefs := cmpDefs.insert d (op, l, r)
      | .load sz d base off =>
        ranges := ranges.insert d (VRange.forMemSize sz)
        if let some so := stackOffs.get? base then
          if let some combined := fitsInt16 (so + off.toInt) then
            changed := true
            s1 := .loadStack sz d combined
        else if let some (base0, k) := addOffs.get? base then
          if let some combined := fitsInt16 (k + off.toInt) then
            changed := true
            s1 := .load sz d base0 combined
        -- Local load-CSE after address/stack folding!
        match s1 with
        | .load lsz ld lbase loff =>
          let key := (lbase, loff.toInt, memSizeTag lsz)
          match localLoads.get? key with
          | some prev =>
            changed := true
            aliases := aliases.insert ld prev
            s1 := .mov ld prev
          | none =>
            localLoads := localLoads.insert key ld
        | .loadStack lsz ld loff =>
          let key := (loff.toInt, memSizeTag lsz)
          match localStackLoads.get? key with
          | some prev =>
            changed := true
            aliases := aliases.insert ld prev
            s1 := .mov ld prev
          | none =>
            localStackLoads := localStackLoads.insert key ld
        | _ => pure ()
      | .loadStack sz d off =>
        ranges := ranges.insert d (VRange.forMemSize sz)
        let key := (off.toInt, memSizeTag sz)
        match localStackLoads.get? key with
        | some prev =>
          changed := true
          aliases := aliases.insert d prev
          s1 := .mov d prev
        | none =>
          localStackLoads := localStackLoads.insert key d
      | .store sz base off val =>
        -- Fold stack base, register offset, AND immediate value into 1-insn `storeStackImm` / `storeImm`!
        let valImm? : Option Int32 :=
          match consts.get? val with
          | some cv => fitsInt32U64 cv
          | none => none
        if let some so := stackOffs.get? base then
          if let some combined := fitsInt16 (so + off.toInt) then
            changed := true
            s1 := match valImm? with
              | some i32 => .storeStackImm sz combined i32
              | none => .storeStack sz combined val
        else if let some (base0, k) := addOffs.get? base then
          if let some combined := fitsInt16 (k + off.toInt) then
            changed := true
            s1 := match valImm? with
              | some i32 => .storeImm sz base0 combined i32
              | none => .store sz base0 combined val
        else if let some i32 := valImm? then
          changed := true
          s1 := .storeImm sz base off i32
        -- Update load-CSE / store-to-load forwarding tables safely:
        -- ANY store invalidates BOTH `localLoads` and `localStackLoads` (prevents stackAddr aliasing),
        -- and only 64-bit (`.b8`) stores forward directly (narrower widths zero-extend on load!).
        localLoads := {}
        localStackLoads := {}
        match s1 with
        | .store .b8 sbase soff sval =>
          localLoads := localLoads.insert (sbase, soff.toInt, memSizeTag .b8) sval
        | .storeStack .b8 soff sval =>
          localStackLoads := localStackLoads.insert (soff.toInt, memSizeTag .b8) sval
        | _ => pure ()
      | .storeImm sz base off imm =>
        if let some so := stackOffs.get? base then
          if let some combined := fitsInt16 (so + off.toInt) then
            changed := true
            s1 := .storeStackImm sz combined imm
        else if let some (base0, k) := addOffs.get? base then
          if let some combined := fitsInt16 (k + off.toInt) then
            changed := true
            s1 := .storeImm sz base0 combined imm
        localLoads := {}
        localStackLoads := {}
      | .storeStack sz off val =>
        if let some cv := consts.get? val then
          if let some i32 := fitsInt32U64 cv then
            changed := true
            s1 := .storeStackImm sz off i32
        localLoads := {}
        localStackLoads := {}
        match s1 with
        | .storeStack .b8 soff sval =>
          localStackLoads := localStackLoads.insert (soff.toInt, memSizeTag .b8) sval
        | _ => pure ()
      | .storeStackImm _ _ _ =>
        localLoads := {}
        localStackLoads := {}
      | .syscall none sym args =>
        localLoads := {}
        localStackLoads := {}
        -- Inline small constant-length `sol_memset_(dst, val, len)` (`<= 5` immediate stores, `<= 40 B`)
        if sym == "sol_memset_" && args.size == 3 then
          let dst := args[0]!
          match consts.get? args[1]!, consts.get? args[2]! with
          | some cv, some clen =>
            if clen == 0 then
              changed := true
              keepStmt := false
            else if let some stores := planMemsetStores cv.toUInt8 clen.toNat 5 then
              changed := true
              keepStmt := false
              for (msz, moff, mimm) in stores do
                let stStmt : Stmt :=
                  if let some so := stackOffs.get? dst then
                    match fitsInt16 (so + moff.toInt) with
                    | some combined => .storeStackImm msz combined mimm
                    | none => .storeImm msz dst moff mimm
                  else if let some (base0, k) := addOffs.get? dst then
                    match fitsInt16 (k + moff.toInt) with
                    | some combined => .storeImm msz base0 combined mimm
                    | none => .storeImm msz dst moff mimm
                  else .storeImm msz dst moff mimm
                outStmts := outStmts.push stStmt
          | _, _ => pure ()
      | .call _ _ _ | .syscall _ _ _ =>
        localLoads := {}
        localStackLoads := {}
      | _ => pure ()
      if keepStmt then
        outStmts := outStmts.push s1

    -- Optimize terminator: alias substitution + compare-branch fusion + range/const fold
    let getRangeT (v : VReg) : VRange :=
      match consts.get? v with
      | some c => VRange.exact c
      | none => ranges.getD v VRange.top
    let t0 := substTerm aliases blk.term
    if t0 != blk.term then changed := true
    let mut t1 : Term := t0
    match t0 with
    | .br c tBlk tArgs eBlk eArgs =>
      match consts.get? c with
      | some cv =>
        changed := true
        t1 := if cv != 0 then .jmp tBlk tArgs else .jmp eBlk eArgs
      | none =>
        match cmpDefs.get? c with
        | some (op, l, r) =>
          let l' := resolveAlias aliases l
          let r' := resolveAlias aliases r
          changed := true
          match consts.get? r' with
          | some cr =>
            match fitsInt32U64 cr with
            | some i32 => t1 := .brCmpImm op l' i32 tBlk tArgs eBlk eArgs
            | none => t1 := .brCmp op l' r' tBlk tArgs eBlk eArgs
          | none =>
            t1 := .brCmp op l' r' tBlk tArgs eBlk eArgs
        | none =>
          changed := true
          t1 := .brCmpImm .ne c 0 tBlk tArgs eBlk eArgs
    | .brCmp op l r tBlk tArgs eBlk eArgs =>
      match consts.get? l, consts.get? r with
      | some cl, some cr =>
        changed := true
        t1 := if op.evalU64 cl cr then .jmp tBlk tArgs else .jmp eBlk eArgs
      | _, _ =>
        match VRange.evalCmp? op (getRangeT l) (getRangeT r) with
        | some b =>
          changed := true
          t1 := if b then .jmp tBlk tArgs else .jmp eBlk eArgs
        | none =>
          match consts.get? l, consts.get? r with
          | _, some cr =>
            if let some i32 := fitsInt32U64 cr then
              changed := true
              t1 := .brCmpImm op l i32 tBlk tArgs eBlk eArgs
          | some cl, none =>
            if let some i32 := fitsInt32U64 cl then
              changed := true
              t1 := .brCmpImm op.flip r i32 tBlk tArgs eBlk eArgs
          | _, _ => pure ()
    | .brCmpImm op l imm tBlk tArgs eBlk eArgs =>
      let cr : UInt64 := Int64.toUInt64 (Int64.ofInt imm.toInt)
      match consts.get? l with
      | some cl =>
        changed := true
        t1 := if op.evalU64 cl cr then .jmp tBlk tArgs else .jmp eBlk eArgs
      | none =>
        let mut fused := false
        if let some b := VRange.evalCmp? op (getRangeT l) (VRange.exact cr) then
          changed := true
          fused := true
          t1 := if b then .jmp tBlk tArgs else .jmp eBlk eArgs
        if !fused && (op == .eq || op == .ne) && imm == 0 then
          if let some (cOp, a, b) := cmpDefs.get? l then
            let a' := resolveAlias aliases a
            let b' := resolveAlias aliases b
            let effOp := if op == .eq then cOp.invert else cOp
            changed := true
            fused := true
            match consts.get? a', consts.get? b' with
            | some ca, some cb =>
              t1 := if effOp.evalU64 ca cb then .jmp tBlk tArgs else .jmp eBlk eArgs
            | _, some cb =>
              match fitsInt32U64 cb with
              | some i32 => t1 := .brCmpImm effOp a' i32 tBlk tArgs eBlk eArgs
              | none => t1 := .brCmp effOp a' b' tBlk tArgs eBlk eArgs
            | some ca, none =>
              match fitsInt32U64 ca with
              | some i32 => t1 := .brCmpImm effOp.flip b' i32 tBlk tArgs eBlk eArgs
              | none => t1 := .brCmp effOp a' b' tBlk tArgs eBlk eArgs
            | none, none =>
              t1 := .brCmp effOp a' b' tBlk tArgs eBlk eArgs
        if !fused && tBlk == eBlk && tArgs == eArgs then
          changed := true
          t1 := .jmp tBlk tArgs
    | _ => pure ()

    newBlocks := newBlocks.push { blk with stmts := outStmts, term := t1 }

  return ({ f with blocks := newBlocks }, changed)

/-- Dead Code & Dead Block-Parameter Elimination. -/
private def dcePass (f : Func) : Func × Bool := Id.run do
  let mut used : Std.HashSet VReg := {}
  for blk in f.blocks do
    for r in blk.term.usedRegs do
      used := used.insert r
    for s in blk.stmts do
      if s.hasSideEffect then
        for r in s.usedRegs do
          used := used.insert r
  let mut progress := true
  while progress do
    progress := false
    for blk in f.blocks do
      for s in blk.stmts do
        if let some d := s.defReg? then
          if used.contains d then
            for r in s.usedRegs do
              if !used.contains r then
                used := used.insert r
                progress := true

  let mut liveParamMask : Std.HashMap BlockId (Array Bool) := {}
  for blk in f.blocks do
    if !blk.params.isEmpty then
      let mask := blk.params.map (fun p => used.contains p)
      if mask.any (· == false) then
        liveParamMask := liveParamMask.insert blk.id mask

  let filterEdge (tgt : BlockId) (args : Array VReg) : Array VReg :=
    match liveParamMask.get? tgt with
    | none => args
    | some mask => Id.run do
      let mut out : Array VReg := #[]
      for i in [0:min mask.size args.size] do
        if mask[i]! then out := out.push args[i]!
      return out

  let mut changed := false
  let mut newBlocks : Array Block := Array.emptyWithCapacity f.blocks.size
  for blk in f.blocks do
    let newParams :=
      match liveParamMask.get? blk.id with
      | none => blk.params
      | some mask => Id.run do
        let mut ps : Array VReg := #[]
        for i in [0:mask.size] do
          if mask[i]! then ps := ps.push blk.params[i]!
        return ps
    if newParams != blk.params then changed := true
    let newTerm :=
      match blk.term with
      | .jmp t a => .jmp t (filterEdge t a)
      | .br c t ta e ea => .br c t (filterEdge t ta) e (filterEdge e ea)
      | .brCmp op l r t ta e ea => .brCmp op l r t (filterEdge t ta) e (filterEdge e ea)
      | .brCmpImm op l imm t ta e ea => .brCmpImm op l imm t (filterEdge t ta) e (filterEdge e ea)
      | other => other
    if newTerm != blk.term then changed := true
    let mut kept : Array Stmt := Array.emptyWithCapacity blk.stmts.size
    for s in blk.stmts do
      if s.hasSideEffect then
        kept := kept.push s
      else
        match s.defReg? with
        | some d =>
          if used.contains d then kept := kept.push s
          else changed := true
        | none => kept := kept.push s
    newBlocks := newBlocks.push { blk with params := newParams, stmts := kept, term := newTerm }
  return ({ f with blocks := newBlocks }, changed)

/-- Tail Merging + Forwarding-Trampoline Collapse + Unreachable Block Pruning.
    Merges all identical constant-return exit blocks (e.g. multiple `Err.invalidAccountData`
    exits share ONE 2-slot `lddw r0, err; exit` tail block — slashes `.so` size!). -/
private def cfgCleanupPass (f : Func) : Func × Bool := Id.run do
  let mut fwd : Std.HashMap BlockId BlockId := {}
  -- 1. Detect trivial forwarding blocks `bbK(ps): jmp bbT(ps)`
  for blk in f.blocks do
    if blk.id != 0 && blk.stmts.isEmpty then
      match blk.term with
      | .jmp tgt args =>
        if tgt != blk.id && args == blk.params then
          fwd := fwd.insert blk.id tgt
      | _ => pure ()

  -- 2. Tail-merge identical constant-return exit blocks: `bbK(): v = const C; ret v`
  let mut constExitCanon : Std.HashMap UInt64 BlockId := {}
  for blk in f.blocks do
    if blk.id != 0 && blk.params.isEmpty && blk.stmts.size == 1 then
      match blk.stmts[0]!, blk.term with
      | .constImm d cv, .ret rv =>
        if d == rv then
          match constExitCanon.get? cv with
          | some canonId =>
            if canonId != blk.id then
              fwd := fwd.insert blk.id canonId
          | none =>
            constExitCanon := constExitCanon.insert cv blk.id
      | _, _ => pure ()

  -- 3. Tail-merge empty variable-return exit blocks `bbK(): ret v` into ONE shared `ret(p)` block!
  --    Eliminates long live ranges & hot-path stack spills on every fallible helper call's `rc`!
  let mut varRetMap : Std.HashMap BlockId VReg := {}
  let mut existingSharedRet? : Option BlockId := none
  let mut maxBid : BlockId := 0
  for blk in f.blocks do
    if blk.id > maxBid then maxBid := blk.id
    if blk.id != 0 && blk.stmts.isEmpty then
      match blk.term with
      | .ret rv =>
        if blk.params.isEmpty then
          varRetMap := varRetMap.insert blk.id rv
        else if blk.params.size == 1 && blk.params[0]! == rv then
          existingSharedRet? := some blk.id
      | _ => pure ()

  let resolveBlk (b : BlockId) : BlockId := Id.run do
    let mut cur := b
    for _ in [0:16] do
      match fwd.get? cur with
      | some nxt => cur := nxt
      | none => break
    return cur

  let mut nextVReg := f.nextVReg
  let mut extraSharedRet? : Option Block := none
  let mut sharedRetId? : Option BlockId := none
  if !varRetMap.isEmpty then
    match existingSharedRet? with
    | some sid => sharedRetId? := some sid
    | none =>
      let sid := maxBid + 1
      let retP := nextVReg
      nextVReg := nextVReg + 1
      extraSharedRet? := some { id := sid, params := #[retP], stmts := #[], term := .ret retP }
      sharedRetId? := some sid

  let rewriteEdge (t : BlockId) (a : Array VReg) : BlockId × Array VReg × Bool :=
    let t1 := resolveBlk t
    match sharedRetId?, varRetMap.get? t1 with
    | some sid, some rv =>
      if a.isEmpty then (sid, #[rv], true)
      else (t1, a, t1 != t)
    | _, _ => (t1, a, t1 != t)

  let mut changed := false
  let mut rewritten : Array Block := Array.emptyWithCapacity (f.blocks.size + 1)
  for blk in f.blocks do
    let mut t' := blk.term
    match blk.term with
    | .jmp t a =>
      let (t2, a2, c) := rewriteEdge t a
      if c then changed := true
      t' := .jmp t2 a2
    | .br c t ta e ea =>
      let (t2, ta2, c1) := rewriteEdge t ta
      let (e2, ea2, c2) := rewriteEdge e ea
      if c1 || c2 then changed := true
      t' := .br c t2 ta2 e2 ea2
    | .brCmp op l r t ta e ea =>
      let (t2, ta2, c1) := rewriteEdge t ta
      let (e2, ea2, c2) := rewriteEdge e ea
      if c1 || c2 then changed := true
      t' := .brCmp op l r t2 ta2 e2 ea2
    | .brCmpImm op l imm t ta e ea =>
      let (t2, ta2, c1) := rewriteEdge t ta
      let (e2, ea2, c2) := rewriteEdge e ea
      if c1 || c2 then changed := true
      t' := .brCmpImm op l imm t2 ta2 e2 ea2
    | _ => pure ()
    rewritten := rewritten.push { blk with term := t' }
  if let some sBlk := extraSharedRet? then
    rewritten := rewritten.push sBlk
    changed := true

  -- BFS reachability from block 0
  let mut blkMap : Std.HashMap BlockId Block := {}
  for blk in rewritten do blkMap := blkMap.insert blk.id blk
  let mut visited : Std.HashSet BlockId := {}
  let mut queue : Array BlockId := #[0]
  visited := visited.insert 0
  let mut qi := 0
  while qi < queue.size do
    let bid := queue[qi]!
    qi := qi + 1
    if let some blk := blkMap.get? bid then
      for s in blk.term.succs do
        if !visited.contains s then
          visited := visited.insert s
          queue := queue.push s

  let kept := rewritten.filter (fun b => visited.contains b.id)
  if kept.size != rewritten.size then changed := true
  return ({ f with blocks := kept, nextVReg := nextVReg }, changed)

/-- Balanced Binary-Search Switch Dispatch Pass:
    Detects linear `if disc == c0 then t0 else if disc == c1 then t1 ...` dispatch chains
    with `>= 6` distinct unsigned constant cases on the same discriminant `disc` and
    rewrites them into a balanced O(log2 N) binary search tree (`brCmpImm .ult`)! -/
private def switchDispatchPass (f : Func) : Func × Bool := Id.run do
  let mut blkMap : Std.HashMap BlockId Block := {}
  let mut maxBid : BlockId := 0
  for b in f.blocks do
    blkMap := blkMap.insert b.id b
    if b.id > maxBid then maxBid := b.id

  -- Count incoming predecessors for each block so we only rewrite internal chain blocks with 1 pred
  let mut predCount : Std.HashMap BlockId Nat := {}
  for b in f.blocks do
    for s in b.term.succs do
      predCount := predCount.insert s (predCount.getD s 0 + 1)

  let mut rewritten := false
  let mut updatedMap := blkMap
  let mut nextBid := maxBid + 1
  let mut extraBlocks : Array Block := #[]

  for blk in f.blocks do
    match (updatedMap.getD blk.id blk).term with
    | .brCmpImm .eq disc c0 t0 #[] e0 #[] =>
      if c0.toInt >= 0 then
        -- Follow linear equality chain on `disc`
        let mut cases : Array (Int32 × BlockId) := #[(c0, t0)]
        let mut seenKeys : Std.HashSet Int := ({} : Std.HashSet Int).insert c0.toInt
        let mut curId := e0
        let mut defaultBlk := e0
        let mut chainIds : Array BlockId := #[]
        for _ in [0:64] do
          if predCount.getD curId 0 != 1 then break
          match updatedMap.get? curId with
          | some nb =>
            if nb.params.isEmpty && nb.stmts.isEmpty then
              match nb.term with
              | .brCmpImm .eq disc2 ck tk #[] ek #[] =>
                if disc2 == disc && ck.toInt >= 0 && !seenKeys.contains ck.toInt then
                  cases := cases.push (ck, tk)
                  seenKeys := seenKeys.insert ck.toInt
                  chainIds := chainIds.push curId
                  curId := ek
                  defaultBlk := ek
                else break
              | _ => break
            else break
          | none => break
        if cases.size >= 6 then
          -- Sort cases by unsigned/non-negative key ascending
          let sorted := cases.qsort (fun a b => a.1.toInt < b.1.toInt)
          -- Build balanced binary search tree recursively using iterative/fuel helper
          let rec buildTree (lo hi : Nat) (fuel : Nat)
              (nb : BlockId) (ex : Array Block) : Term × BlockId × Array Block :=
            match fuel with
            | 0 => (.jmp defaultBlk #[], nb, ex)
            | fuel' + 1 =>
              let len := hi - lo
              if len == 0 then
                (.jmp defaultBlk #[], nb, ex)
              else if len == 1 then
                let (ck, tk) := sorted[lo]!
                (.brCmpImm .eq disc ck tk #[] defaultBlk #[], nb, ex)
              else if len == 2 then
                let (cA, tA) := sorted[lo]!
                let (cB, tB) := sorted[lo + 1]!
                let bId := nb
                let bBlk : Block := { id := bId, params := #[], stmts := #[],
                                      term := .brCmpImm .eq disc cB tB #[] defaultBlk #[] }
                (.brCmpImm .eq disc cA tA #[] bId #[], nb + 1, ex.push bBlk)
              else
                let mid := lo + len / 2
                let midKey := sorted[mid]!.1
                let (lTerm, nb1, ex1) := buildTree lo mid fuel' nb ex
                let lId := nb1
                let lBlk : Block := { id := lId, params := #[], stmts := #[], term := lTerm }
                let (rTerm, nb2, ex2) := buildTree mid hi fuel' (nb1 + 1) (ex1.push lBlk)
                let rId := nb2
                let rBlk : Block := { id := rId, params := #[], stmts := #[], term := rTerm }
                (.brCmpImm .ult disc midKey lId #[] rId #[], nb2 + 1, ex2.push rBlk)
          let (rootTerm, nb', ex') := buildTree 0 sorted.size 32 nextBid extraBlocks
          nextBid := nb'
          extraBlocks := ex'
          let curBlk := updatedMap.getD blk.id blk
          updatedMap := updatedMap.insert blk.id { curBlk with term := rootTerm }
          rewritten := true
    | _ => pure ()

  if !rewritten then return (f, false)
  let mut outBlocks : Array Block := Array.emptyWithCapacity (f.blocks.size + extraBlocks.size)
  for b in f.blocks do
    outBlocks := outBlocks.push (updatedMap.getD b.id b)
  outBlocks := outBlocks ++ extraBlocks
  return ({ f with blocks := outBlocks }, true)

/-- Run all IR optimization passes to a fixed point (bounded to 12 iterations). -/
def optimizeFunc (f : Func) : Func := Id.run do
  let mut cur := f
  for _ in [0:12] do
    let (f1, c1) := forwardOptPass cur
    let (f2, c2) := dcePass f1
    let (f3, c3) := cfgCleanupPass f2
    cur := f3
    if !c1 && !c2 && !c3 then break
  let (fSw, cSw) := switchDispatchPass cur
  if cSw then
    let (fClean, _) := cfgCleanupPass fSw
    return fClean
  return cur

/-! ### Interprocedural Dead Helper Elimination (`removeDeadHelpers`) -/

/-- All helper labels directly called by `Stmt.call` inside `f`. -/
def Func.calledLabels (f : Func) : List String :=
  f.blocks.toList.flatMap fun blk =>
    blk.stmts.toList.filterMap fun s =>
      match s with
      | .call _ lbl _ => some lbl
      | _ => none

/-- Deduplicated append of `xs` into `acc`. -/
def addUniqueLabels (acc : List String) (xs : List String) : List String :=
  xs.foldl (fun a lbl => if a.contains lbl then a else lbl :: a) acc

/-- Fixed-point call-graph reachability over `helpers` starting from `reached`:
    each step adds every `calledLabels` of every helper whose `labelPrefix ∈ reached`,
    deduplicated and terminating early at fixed point (`next.length == reached.length`). -/
def expandReachableLabels (helpers : List Func) : Nat → List String → List String
  | 0, reached => reached
  | fuel + 1, reached =>
    let next := helpers.foldl (fun acc h =>
      if acc.contains h.labelPrefix then addUniqueLabels acc h.calledLabels else acc) reached
    if next.length == reached.length then reached
    else expandReachableLabels helpers fuel next

/-- Interprocedural Dead Helper Elimination: removes any outlined helper in `prog.helpers`
    not reachable from `prog.entry` via `Stmt.call` chains (preserving deterministic order). -/
def removeDeadHelpers (prog : Program) : Program :=
  let helpersList := prog.helpers.toList
  let init := addUniqueLabels [] prog.entry.calledLabels
  let reached := expandReachableLabels helpersList helpersList.length init
  { prog with helpers := prog.helpers.filter (fun h => reached.contains h.labelPrefix) }

end LeanSVM.Compiler
