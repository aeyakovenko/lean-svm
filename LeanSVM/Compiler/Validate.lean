/-
  LeanSVM.Compiler.Validate
  Formally verified post-Optimize / post-RegAlloc Translation Validator for `SbfIR`.

  Architecture (shrinking the compiler TCB):
  - `computeLivenessCert` (untrusted): computes candidate `(liveIn, liveOut)` sets over `orderedBlocks`.
  - `checkFuncCFG`, `checkProgramCFG`, `checkAllocCert` (TRUSTED & FORMALLY PROVEN SOUND in
    `LeanSVM.Compiler.Proofs`): tiny, pure, total boolean checkers that independently certify:
    1. CFG integrity: unique block IDs, block 0 present, every edge target exists with exact
       block-parameter arity, every `.call` target exists in `Program.helpers`.
    2. ISA / verifier safety: every shift immediate is in `[0, 63]` / `[0, 31]`; no `sub64`/`sub32`
       immediate uses `Int32.minValue` (guaranteeing sBPF v3 safety).
    3. Register & stack well-formedness: every allocated reg is in `r1..r9` (never `r0` or `r10`),
       every spill slot is 8-byte aligned, strictly disjoint from user `stackAllocBytes`, and within
       the 4096-byte sBPF stack frame (`totalStackBytes ≤ 4096`).
    4. Exact `CodeGen` preconditions: non-`constImm` defs never target `.imm`, `constImm` remats
       match their exact value, `r5` scratch safety holds whenever any 2nd operand or stack move
       uses `r5`, and every call/syscall-crossing live `VReg` resides in callee-saved `r6..r9`,
       `.stack`, or `.imm`.
    5. Pairwise live-range non-interference: at every statement def and every block-parameter entry,
       no two simultaneously live `VReg`s share a physical register or overlapping stack slot
       (`Int.natAbs (o1 - o2) < 8`), backed by verified backward dataflow fixed-point inequations!
-/
import LeanSVM.Compiler.IR
import LeanSVM.Compiler.RegAlloc
import LeanSVM.Compiler.CodeGen
import Std.Data.HashMap
import Std.Data.HashSet

namespace LeanSVM.Compiler

open LeanSVM.SBPF

/-! ### 1. Pure Decidable Predicates (Proved Sound in `LeanSVM.Compiler.Proofs`) -/

/-- Outgoing `(targetBlockId, edgeArgs)` edges of a terminator. -/
def Term.edges : Term → List (BlockId × Array VReg)
  | .jmp tgt args                  => [(tgt, args)]
  | .br _ t ta e ea                => [(t, ta), (e, ea)]
  | .brCmp _ _ _ t ta e ea         => [(t, ta), (e, ea)]
  | .brCmpImm _ _ _ t ta e ea      => [(t, ta), (e, ea)]
  | .ret _ | .unreach              => []

/-- Direct operand uses of a terminator (excluding edge arguments). -/
def Term.directUses : Term → List VReg
  | .jmp _ _                => []
  | .br c _ _ _ _           => [c]
  | .brCmp _ l r _ _ _ _    => [l, r]
  | .brCmpImm _ l _ _ _ _ _ => [l]
  | .ret v                  => [v]
  | .unreach                => []

/-- True iff `r` is a callee-saved sBPF register (`r6..r9`). -/
def isCalleeSavedReg (r : Reg) : Bool :=
  6 ≤ r.idx.toNat && r.idx.toNat ≤ 9

/-- True iff `r` is a valid allocatable sBPF register (`r1..r9`, never `r0` scratch or `r10` FP). -/
def isAllocatableReg (r : Reg) : Bool :=
  1 ≤ r.idx.toNat && r.idx.toNat ≤ 9

/-- Aligned user stack allocation size (bytes reserved directly below `r10`). -/
def alignedBaseStack (stackAllocBytes : Nat) : Nat :=
  ((stackAllocBytes + 7) / 8) * 8

/-- True iff a physical `Loc` is valid for a function with `baseStackAligned` and `totalStackBytes`. -/
def locWellFormed (baseStackAligned totalStackBytes : Nat) : Loc → Bool
  | .reg r     => isAllocatableReg r
  | .stack off =>
    off.toInt ≤ -(baseStackAligned : Int) - 8 &&
    -(totalStackBytes : Int) ≤ off.toInt &&
    off.toInt % 8 == 0
  | .imm _     => true

/-- True iff two physical locations alias or overlap in registers or 8-byte stack slots. -/
def locsConflict : Loc → Loc → Bool
  | .reg r1,   .reg r2   => r1 == r2
  | .stack o1, .stack o2 => Int.natAbs (o1.toInt - o2.toInt) < 8
  | _,         _         => false

/-- True iff a `Loc` is preserved across sBPF `call` / `syscall` instructions. -/
def locPreservedAcrossCall : Loc → Bool
  | .reg r   => isCalleeSavedReg r
  | .stack _ => true
  | .imm _   => true

/-- True iff `Stmt` has verifier-legal shift immediates and v3-safe `sub` immediates. -/
def stmtImmWellFormed : Stmt → Bool
  | .binImm op _ _ imm =>
    match op with
    | .lsh64 | .rsh64 | .arsh64 => 0 ≤ imm.toInt && imm.toInt < 64
    | .lsh32 | .rsh32           => 0 ≤ imm.toInt && imm.toInt < 32
    | .sub64 | .sub32           => imm.toInt ≠ -2147483648
    | _                         => true
  | _ => true

/-- Pure lookup of a block by `BlockId` in a block list. -/
def findBlock? (blocks : List Block) (bid : BlockId) : Option Block :=
  blocks.find? (fun b => b.id == bid)

/-- Check that a list has no duplicate keys. -/
def listNoDup [BEq α] : List α → Bool
  | []      => true
  | x :: xs => !xs.contains x && listNoDup xs

/-- Check CFG structural integrity of `blocks` (unique IDs, block 0 exists, all edges match
    existing target blocks with exact parameter arity, and all statement immediates are legal). -/
def checkBlocksCFG (params : Array VReg) (blocks : List Block) : Bool :=
  params.size ≤ 5 &&
  listNoDup (blocks.map (·.id)) &&
  (findBlock? blocks 0).isSome &&
  blocks.all fun blk =>
    listNoDup blk.params.toList &&
    blk.stmts.toList.all stmtImmWellFormed &&
    blk.term.edges.all fun (tgt, args) =>
      match findBlock? blocks tgt with
      | some tb => args.size == tb.params.size
      | none    => false

/-- Check interprocedural `Program` CFG + call-target integrity. -/
def checkProgramCFG (prog : Program) : Bool :=
  let helperLabels := prog.helpers.toList.map (·.labelPrefix)
  let validCallLabel (lbl : String) : Bool := helperLabels.contains lbl
  let checkCalls (f : Func) : Bool :=
    f.blocks.toList.all fun blk =>
      blk.stmts.toList.all fun s =>
        match s with
        | .call _ lbl _ => validCallLabel lbl
        | _             => true
  listNoDup helperLabels &&
  !helperLabels.contains prog.entry.labelPrefix &&
  checkBlocksCFG prog.entry.params prog.entry.blocks.toList &&
  checkCalls prog.entry &&
  prog.helpers.toList.all fun h =>
    checkBlocksCFG h.params h.blocks.toList && checkCalls h

/-- True iff `v` is explicitly allocated in `alloc.locs` to a well-formed location. -/
def vregLocValid (baseStackAligned totalStackBytes : Nat) (alloc : AllocResult) (v : VReg) : Bool :=
  match alloc.locs.get? v with
  | some loc => locWellFormed baseStackAligned totalStackBytes loc
  | none     => false

/-- True iff `stmt`'s defined destination `VReg` (if any) satisfies `CodeGen` destination invariants:
    - explicitly allocated to a well-formed location (hence never `r0` or `r10`)
    - non-`constImm` statements NEVER write to `.imm _`
    - `constImm d val` rematerialized as `.imm v` satisfies `v == val`. -/
def stmtDstValid (baseStackAligned totalStackBytes : Nat) (alloc : AllocResult) (s : Stmt) : Bool :=
  match s.defReg? with
  | none => true
  | some d =>
    match alloc.locs.get? d with
    | none => false
    | some loc =>
      locWellFormed baseStackAligned totalStackBytes loc &&
      match s, loc with
      | .constImm _ val, .imm v => v == val
      | _, .imm _               => false
      | _, _                    => true

/-- True iff `v`'s allocated location is a non-register (`.stack _` or `.imm _`). -/
def isNonRegLoc (alloc : AllocResult) (v : VReg) : Bool :=
  match getLoc alloc v with
  | .reg _ => false
  | .stack _ | .imm _ => true

/-- True iff `CodeGen.emitStmt` uses scratch register `r5` when lowering `s` under `alloc`. -/
def stmtUsesScratchR5 (alloc : AllocResult) (s : Stmt) : Bool :=
  match s with
  | .binOp _ _ _ r => isNonRegLoc alloc r
  | .cmp _ _ _ r   => isNonRegLoc alloc r
  | .store _ _ _ v => isNonRegLoc alloc v
  | _              => false

/-- Check `r5` scratch safety and call callee-saved safety for statement `s` with live-after set `liveAfter`. -/
def stmtRegSafety (alloc : AllocResult) (s : Stmt) (liveAfter : List VReg) : Bool :=
  let r5Ok : Bool :=
    if stmtUsesScratchR5 alloc s then
      let operandsOk : Bool :=
        match s with
        | .binOp _ d l _ => getLoc alloc l != .reg Reg.r5 && getLoc alloc d != .reg Reg.r5
        | .cmp _ d l _   => getLoc alloc l != .reg Reg.r5 && getLoc alloc d != .reg Reg.r5
        | .store _ b _ _ => getLoc alloc b != .reg Reg.r5
        | _              => true
      operandsOk && liveAfter.all (fun u => some u == s.defReg? || getLoc alloc u != .reg Reg.r5)
    else true
  let callOk : Bool :=
    if s.isCallLike then
      liveAfter.all (fun u => some u == s.defReg? || locPreservedAcrossCall (getLoc alloc u))
    else true
  r5Ok && callOk

/-- Check pairwise non-conflict among all distinct `VReg`s in `vs`. -/
def pairwiseDisjointLocs (alloc : AllocResult) : List VReg → Bool
  | [] => true
  | v :: rest =>
    rest.all (fun u => u == v || !locsConflict (getLoc alloc v) (getLoc alloc u)) &&
    pairwiseDisjointLocs alloc rest

/-- Pure backward pass checking every statement in a block (given in reverse order, starting from
    `liveAfter` at block exit). Returns `some liveBefore` iff EVERY statement satisfies:
    - `stmtDstValid` & all `usedRegs` well-formed
    - `stmtRegSafety` (`r5` scratch & call callee-saved preservation)
    - non-interference: `defReg` does not conflict with any `u ∈ liveAfter` (`u ≠ defReg`)! -/
def checkStmtsBackward (baseStackAligned totalStackBytes : Nat) (alloc : AllocResult)
    (revStmts : List Stmt) (liveAfter : List VReg) : Option (List VReg) :=
  match revStmts with
  | [] => some liveAfter
  | s :: rest =>
    let dstOk := stmtDstValid baseStackAligned totalStackBytes alloc s
    let usesOk := s.usedRegs.toList.all (vregLocValid baseStackAligned totalStackBytes alloc)
    let regOk := stmtRegSafety alloc s liveAfter
    let interfOk :=
      match s.defReg? with
      | none => true
      | some d =>
        liveAfter.all (fun u => u == d || !locsConflict (getLoc alloc d) (getLoc alloc u))
    if dstOk && usesOk && regOk && interfOk then
      let liveBefore :=
        (liveAfter.filter (fun u => some u != s.defReg?)) ++
        (s.usedRegs.toList.filter (fun u => !liveAfter.contains u || some u == s.defReg?))
      checkStmtsBackward baseStackAligned totalStackBytes alloc rest liveBefore
    else none

/-- Lookup a block's liveness list from a pure association list certificate. -/
def lookupLive (cert : List (BlockId × List VReg)) (bid : BlockId) : List VReg :=
  match cert.find? (fun p => p.1 == bid) with
  | some (_, vs) => vs
  | none         => []

/-- Check whether a parallel move `(dst, src)` requires `memTmp = r5` in `emitSingleLocMove`. -/
def moveUsesMemTmpR5 (dst src : Loc) : Bool :=
  match dst, src with
  | .stack _, .stack _ => true
  | .stack _, .imm v   => (fitsInt32 v).isNone
  | _, _               => false

/-- Pure, total, formally verified Allocation & Liveness Certificate Checker!
    Checks ALL `CodeGen` / `RegAlloc` / stack-frame / liveness / non-interference invariants
    for `f` under `alloc`, using candidate `(liveInCert, liveOutCert)`. -/
def checkAllocCert (f : Func) (alloc : AllocResult)
    (liveInCert liveOutCert : List (BlockId × List VReg)) : Bool :=
  let blocks := alloc.orderedBlocks.toList
  let baseAligned := alignedBaseStack f.stackAllocBytes
  let totalStack := alloc.totalStackBytes
  -- 1. Stack frame within Solana's 4096 B hard limit & covers user stack allocations
  (baseAligned ≤ totalStack) &&
  (totalStack ≤ 4096) &&
  -- 2. CFG structural integrity on the exact `orderedBlocks` compiled by `CodeGen`
  checkBlocksCFG f.params blocks &&
  -- 3. Function parameters well-formed, non-`.imm`, and pairwise location-disjoint
  (f.params.toList.all fun p =>
    vregLocValid baseAligned totalStack alloc p &&
    match getLoc alloc p with | .imm _ => false | _ => true) &&
  pairwiseDisjointLocs alloc f.params.toList &&
  -- 4. Per-block liveness fixed-point + statement/terminator/edge non-interference checks
  blocks.all fun blk =>
    let bIn  := lookupLive liveInCert blk.id
    let bOut := lookupLive liveOutCert blk.id
    -- 4a. Block parameters well-formed, non-`.imm`, pairwise disjoint, and disjoint from live-in passthroughs
    let paramsOk :=
      blk.params.toList.all (fun bp =>
        vregLocValid baseAligned totalStack alloc bp &&
        (match getLoc alloc bp with | .imm _ => false | _ => true) &&
        bIn.all (fun v => blk.params.contains v || !locsConflict (getLoc alloc bp) (getLoc alloc v))) &&
      pairwiseDisjointLocs alloc blk.params.toList
    -- 4b. Outgoing edge fixed-point inequations + edge-move `r5` safety
    let edgesOk :=
      blk.term.edges.all fun (tgtId, args) =>
        match findBlock? blocks tgtId with
        | none => false
        | some tb =>
          let tIn := lookupLive liveInCert tgtId
          let passthroughOk := tIn.all (fun v => tb.params.contains v || bOut.contains v)
          let argsOk := args.toList.all (fun a => bOut.contains a && vregLocValid baseAligned totalStack alloc a)
          let edgeMemTmpOk :=
            let pairs := List.zip tb.params.toList args.toList
            if pairs.any (fun (p, a) => moveUsesMemTmpR5 (getLoc alloc p) (getLoc alloc a)) then
              bOut.all (fun v => getLoc alloc v != .reg Reg.r5) &&
              tb.params.toList.all (fun p => getLoc alloc p != .reg Reg.r5)
            else true
          passthroughOk && argsOk && edgeMemTmpOk
    -- 4c. Terminator direct uses well-formed & `brCmp` `r5` scratch safety
    let termUsesOk := blk.term.directUses.all (vregLocValid baseAligned totalStack alloc)
    let termR5Ok :=
      match blk.term with
      | .brCmp _ l r _ _ _ _ =>
        if isNonRegLoc alloc r then
          getLoc alloc l != .reg Reg.r5 &&
          bOut.all (fun u => getLoc alloc u != .reg Reg.r5)
        else true
      | _ => true
    -- 4d. Backward statement checking from `liveAtTerm = bOut ∪ directUses`
    let liveAtTerm := bOut ++ blk.term.directUses.filter (fun u => !bOut.contains u)
    let stmtsOk :=
      match checkStmtsBackward baseAligned totalStack alloc blk.stmts.toList.reverse liveAtTerm with
      | none => false
      | some liveBefore =>
        -- Fixed-point inequation at block entry: every live-before reg not defined by block/func params is in `bIn`!
        liveBefore.all fun v =>
          blk.params.contains v || (blk.id == 0 && f.params.contains v) || bIn.contains v
    paramsOk && edgesOk && termUsesOk && termR5Ok && stmtsOk

/-! ### 2. Fast Untrusted Liveness Certificate Producer + Public Validator Entrypoints -/

/-- Independently compute exact backward `(liveIn, liveOut)` sets over `orderedBlocks`
    to serve as a liveness certificate for `checkAllocCert`. -/
def computeLivenessCert (f : Func) (blocks : Array Block) :
    List (BlockId × List VReg) × List (BlockId × List VReg) := Id.run do
  let mut blkUse : Std.HashMap BlockId (Std.HashSet VReg) := {}
  let mut blkDef : Std.HashMap BlockId (Std.HashSet VReg) := {}
  let mut blkParams : Std.HashMap BlockId (Std.HashSet VReg) := {}
  for blk in blocks do
    let mut ps : Std.HashSet VReg := {}
    let mut defs : Std.HashSet VReg := {}
    let mut uses : Std.HashSet VReg := {}
    for bp in blk.params do
      ps := ps.insert bp
      defs := defs.insert bp
    if blk.id == 0 then
      for fp in f.params do defs := defs.insert fp
    for s in blk.stmts do
      for u in s.usedRegs do
        if !defs.contains u then uses := uses.insert u
      if let some d := s.defReg? then defs := defs.insert d
    for u in blk.term.usedRegs do
      if !defs.contains u then uses := uses.insert u
    blkParams := blkParams.insert blk.id ps
    blkDef := blkDef.insert blk.id defs
    blkUse := blkUse.insert blk.id uses

  let mut liveIn  : Std.HashMap BlockId (Std.HashSet VReg) := {}
  let mut liveOut : Std.HashMap BlockId (Std.HashSet VReg) := {}
  for blk in blocks do
    liveIn  := liveIn.insert blk.id (blkUse.getD blk.id {})
    let mut out0 : Std.HashSet VReg := {}
    for (_, args) in blk.term.edges do
      for a in args do out0 := out0.insert a
    liveOut := liveOut.insert blk.id out0

  let mut changed := true
  while changed do
    changed := false
    let mut bi := blocks.size
    while bi > 0 do
      bi := bi - 1
      let blk := blocks[bi]!
      let mut outSet := liveOut.getD blk.id {}
      for (s, args) in blk.term.edges do
        let sIn := liveIn.getD s {}
        let sPs := blkParams.getD s {}
        for v in sIn.toList do
          if !sPs.contains v && !outSet.contains v then
            outSet := outSet.insert v
            changed := true
        for a in args do
          if !outSet.contains a then
            outSet := outSet.insert a
            changed := true
      liveOut := liveOut.insert blk.id outSet

      let mut inSet := liveIn.getD blk.id {}
      let bDef := blkDef.getD blk.id {}
      for v in outSet.toList do
        if !bDef.contains v && !inSet.contains v then
          inSet := inSet.insert v
          changed := true
      liveIn := liveIn.insert blk.id inSet

  let inCert := blocks.toList.map fun blk => (blk.id, (liveIn.getD blk.id {}).toList)
  let outCert := blocks.toList.map fun blk => (blk.id, (liveOut.getD blk.id {}).toList)
  return (inCert, outCert)

/-- Validate `alloc` for `f` via the formally verified certificate checker `checkAllocCert`. -/
def validateFuncAlloc (f : Func) (alloc : AllocResult) : Except String Unit :=
  let (inCert, outCert) := computeLivenessCert f alloc.orderedBlocks
  if checkAllocCert f alloc inCert outCert then
    .ok ()
  else
    .error s!"[lean-svm] translation validation failed for function '{f.name}' (CFG / liveness / register-allocation soundness violation)"

/-- Validate interprocedural `Program` CFG & call-graph invariants. -/
def validateProgramCFG (prog : Program) : Except String Unit :=
  if checkProgramCFG prog then
    .ok ()
  else
    .error s!"[lean-svm] translation validation failed for program '{prog.entry.name}' (CFG / call-graph / immediate invariant violation)"

/-! ### 3. Formally Verified Post-Peephole Final sBPF Instruction-Stream Validator -/

/-- Memory access byte width for `MemSize`. -/
def memSizeBytes : MemSize → Int
  | .b1 => 1
  | .b2 => 2
  | .b4 => 4
  | .b8 => 8

/-- Valid sBPF register index (`r0..r10`). -/
def isValidSbpfReg (r : Reg) : Bool :=
  r.idx.toNat ≤ 10

/-- Writable sBPF register (`r0..r9`, NEVER read-only stack frame pointer `r10`). -/
def isWritableSbpfReg (r : Reg) : Bool :=
  r.idx.toNat ≤ 9

/-- Check stack-frame bounds for any `r10`-relative memory access: strictly inside `[-4096, -width]`. -/
def stackAccessLegal (base : Reg) (sz : MemSize) (off : Int16) : Bool :=
  if base == Reg.r10 then
    (-4096 : Int) ≤ off.toInt && off.toInt + memSizeBytes sz ≤ 0
  else true

/-- Check ALU immediate legality for strict sBPF v3. -/
def sbpfAluImmLegal (is64 : Bool) (op : AluOp) (imm : Int32) : Bool :=
  match op with
  | .lsh | .rsh | .arsh =>
    0 ≤ imm.toInt && imm.toInt < (if is64 then 64 else 32)
  | .sub => imm.toInt ≠ -2147483648
  | .div | .mod => imm.toInt ≠ 0
  | _ => true

/-- Pure, total Agave sBPF v3 instruction-level safety predicate checked on EVERY emitted
    instruction AFTER `SBPF.peepholeOptimize` and BEFORE `SBPF.emitElf`! -/
def checkSbpfInsn (labels : Std.HashSet String) : Insn → Bool
  | .label _ => true
  | .alu64Reg _ d s => isWritableSbpfReg d && isValidSbpfReg s
  | .alu64Imm op d imm => isWritableSbpfReg d && sbpfAluImmLegal true op imm
  | .alu32Reg _ d s => isWritableSbpfReg d && isValidSbpfReg s
  | .alu32Imm op d imm => isWritableSbpfReg d && sbpfAluImmLegal false op imm
  | .neg64 d => isWritableSbpfReg d
  | .lddw d _ => isWritableSbpfReg d
  | .lddwRodata d _ => isWritableSbpfReg d
  | .ldx sz d base off =>
    isWritableSbpfReg d && isValidSbpfReg base && stackAccessLegal base sz off
  | .stx sz base src off =>
    isValidSbpfReg base && isValidSbpfReg src && stackAccessLegal base sz off
  | .stImm sz base off _ =>
    isValidSbpfReg base && stackAccessLegal base sz off
  | .ja tgt => labels.contains tgt
  | .jccReg _ d s tgt => isValidSbpfReg d && isValidSbpfReg s && labels.contains tgt
  | .jccImm _ d _ tgt => isValidSbpfReg d && labels.contains tgt
  | .callLocal tgt => labels.contains tgt
  | .callSyscall _ => true
  | .exit => true

/-- Extract the last non-label instruction in a list (verifying no fall-through past end of `.text`). -/
def lastNonLabel? : List Insn → Option Insn
  | [] => none
  | .label _ :: rest => lastNonLabel? rest
  | insn :: rest =>
    match lastNonLabel? rest with
    | some last => some last
    | none => some insn

/-- Pure post-peephole sBPF stream certificate checker:
    1. Unique label definitions (no duplicate jump targets)
    2. Every instruction satisfies `checkSbpfInsn` (valid regs, `r10` read-only, stack `[-4096, -width]`,
       legal shift/div/mod/sub32/64 immediates, every jump/call target resolves to a defined label)
    3. Final non-label instruction is `.exit` or `.ja _` (zero fall-through past `.text`!). -/
def checkSbpfProgram (insns : List Insn) : Bool :=
  let (labels, uniqueOk) := insns.foldl
    (fun (acc : Std.HashSet String × Bool) insn =>
      match insn with
      | .label name =>
        if acc.1.contains name then (acc.1, false) else (acc.1.insert name, acc.2)
      | _ => acc)
    ({}, true)
  let endsCleanly :=
    match lastNonLabel? insns with
    | some .exit | some (.ja _) => true
    | _ => false
  uniqueOk && endsCleanly && insns.all (checkSbpfInsn labels)

/-- Soundness theorem for post-peephole sBPF translation validation:
    whenever `checkSbpfProgram insns = true`, EVERY emitted instruction in `insns` satisfies
    `checkSbpfInsn` against the exact unique label set AND the stream terminates cleanly! -/
theorem checkSbpfProgram_sound (insns : List Insn) (h : checkSbpfProgram insns = true) :
    let labels := (insns.foldl
      (fun (acc : Std.HashSet String × Bool) insn =>
        match insn with
        | .label name =>
          if acc.1.contains name then (acc.1, false) else (acc.1.insert name, acc.2)
        | _ => acc)
      ({}, true)).1
    (∀ insn ∈ insns, checkSbpfInsn labels insn = true) ∧
    (lastNonLabel? insns = some .exit ∨ ∃ tgt, lastNonLabel? insns = some (.ja tgt)) := by
  unfold checkSbpfProgram at h
  dsimp only at h
  simp only [Bool.and_eq_true] at h
  refine ⟨fun insn hmem => List.all_eq_true.mp h.2 insn hmem, ?_⟩
  have hend := h.1.2
  cases hl : lastNonLabel? insns with
  | none => rw [hl] at hend; cases hend
  | some i =>
    rw [hl] at hend
    cases i with
    | exit => exact Or.inl rfl
    | ja tgt => exact Or.inr ⟨tgt, rfl⟩
    | _ => cases hend

/-- Validate the final post-peephole sBPF instruction stream right before ELF emission. -/
def validateSbpfProgram (entryName : String) (insns : Array Insn) : Except String Unit :=
  if checkSbpfProgram insns.toList then
    .ok ()
  else
    .error s!"[lean-svm] post-peephole sBPF translation validation failed for '{entryName}'"

end LeanSVM.Compiler
