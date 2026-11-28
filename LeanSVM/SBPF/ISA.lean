/-
  LeanSVM.SBPF.ISA
  Native Solana sBPF v3 (SIMD-0178 static syscalls + SIMD-0189 strict ELF + SIMD-0377)
  Instruction Set Architecture, exact 8-byte little-endian machine code encoder,
  Murmur3-32 static syscall hasher, and built-in disassembler.
-/

namespace LeanSVM.SBPF

/-- Physical sBPF registers (`r0`..`r10`).
    - `r0`: return value / scratch
    - `r1..r5`: arguments / caller-saved scratch
    - `r6..r9`: callee-saved (preserved across syscalls & internal calls)
    - `r10`: read-only stack frame pointer -/
structure Reg where
  idx : UInt8
  deriving Repr, BEq, DecidableEq, Hashable, Inhabited

namespace Reg
  def r0  : Reg := ⟨0⟩
  def r1  : Reg := ⟨1⟩
  def r2  : Reg := ⟨2⟩
  def r3  : Reg := ⟨3⟩
  def r4  : Reg := ⟨4⟩
  def r5  : Reg := ⟨5⟩
  def r6  : Reg := ⟨6⟩
  def r7  : Reg := ⟨7⟩
  def r8  : Reg := ⟨8⟩
  def r9  : Reg := ⟨9⟩
  def r10 : Reg := ⟨10⟩

  def toString (r : Reg) : String := s!"r{r.idx}"
  instance : ToString Reg := ⟨Reg.toString⟩
end Reg

/-- Memory access width in bytes. -/
inductive MemSize where
  | b1 | b2 | b4 | b8
  deriving Repr, BEq, DecidableEq

/-- ALU operation code. -/
inductive AluOp where
  | add | sub | mul | div | or | and | lsh | rsh | mod | xor | mov | arsh
  deriving Repr, BEq, DecidableEq

/-- True iff Solana sBPF v3 sign-extends the 32-bit result of `op` into
    bits `32..63` (`i32 → i64 → u64`) instead of zero-extending (`u32 → u64`). -/
def AluOp.signExtendsInAlu32 : AluOp → Bool
  | .add | .sub | .mul => true
  | _ => false

/-- Conditional jump predicate. -/
inductive JmpCond where
  | eq | gt | ge | set | ne | sgt | sge | lt | le | slt | sle
  deriving Repr, BEq, DecidableEq

namespace JmpCond
  /-- Logical negation of a branch condition (used for fallthrough optimization). -/
  def invert : JmpCond → Option JmpCond
    | .eq  => some .ne
    | .ne  => some .eq
    | .gt  => some .le
    | .le  => some .gt
    | .ge  => some .lt
    | .lt  => some .ge
    | .sgt => some .sle
    | .sle => some .sgt
    | .sge => some .slt
    | .slt => some .sge
    | .set => none

  def mnemonic : JmpCond → String
    | .eq  => "jeq"
    | .gt  => "jgt"
    | .ge  => "jge"
    | .set => "jset"
    | .ne  => "jne"
    | .sgt => "jsgt"
    | .sge => "jsge"
    | .lt  => "jlt"
    | .le  => "jle"
    | .slt => "jslt"
    | .sle => "jsle"
end JmpCond

/-- Symbolic sBPF instruction (before label offset resolution). -/
inductive Insn where
  | label (name : String)
  | alu64Reg (op : AluOp) (dst src : Reg)
  | alu64Imm (op : AluOp) (dst : Reg) (imm : Int32)
  | alu32Reg (op : AluOp) (dst src : Reg)
  | alu32Imm (op : AluOp) (dst : Reg) (imm : Int32)
  | neg64 (dst : Reg)
  | lddw (dst : Reg) (imm : UInt64)
  | lddwRodata (dst : Reg) (rodataOff : UInt32)
  | ldx (sz : MemSize) (dst src : Reg) (off : Int16)
  | stx (sz : MemSize) (dst src : Reg) (off : Int16)
  | stImm (sz : MemSize) (dst : Reg) (off : Int16) (imm : Int32)
  | ja (target : String)
  | jccReg (cond : JmpCond) (dst src : Reg) (target : String)
  | jccImm (cond : JmpCond) (dst : Reg) (imm : Int32) (target : String)
  | callLocal (target : String)
  | callSyscall (symName : String)
  | exit
  deriving Repr, BEq, Inhabited

/-- Number of 8-byte sBPF instruction slots occupied by an instruction. -/
def Insn.slotCount : Insn → Nat
  | .label _        => 0
  | .lddw _ _       => 2
  | .lddwRodata _ _ => 2
  | _               => 1

/-! ### Little-Endian ByteArray Encoding Helpers -/

def pushU16LE (buf : ByteArray) (v : UInt16) : ByteArray :=
  buf
    |>.push (v &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8

def pushU32LE (buf : ByteArray) (v : UInt32) : ByteArray :=
  buf
    |>.push (v &&& 0xFF).toUInt8
    |>.push ((v >>> 8) &&& 0xFF).toUInt8
    |>.push ((v >>> 16) &&& 0xFF).toUInt8
    |>.push ((v >>> 24) &&& 0xFF).toUInt8

def pushU64LE (buf : ByteArray) (v : UInt64) : ByteArray :=
  let lo := v.toUInt32
  let hi := (v >>> 32).toUInt32
  pushU32LE (pushU32LE buf lo) hi

/-- Encode one 8-byte raw sBPF instruction word: `[opc, (src<<4)|dst, off_lo, off_hi, imm0..3]`. -/
def pushRawInsn (buf : ByteArray) (opc : UInt8) (dst src : UInt8) (off : Int16) (imm : UInt32) : ByteArray :=
  let regs : UInt8 := ((src &&& 0x0F) <<< 4) ||| (dst &&& 0x0F)
  let offU : UInt16 := off.toUInt16
  let b1 := buf.push opc |>.push regs
  let b2 := pushU16LE b1 offU
  pushU32LE b2 imm

/-! ### Exact Solana sBPF Opcode Tables -/

def aluBaseOpc : AluOp → UInt8
  | .add  => 0x00
  | .sub  => 0x10
  | .mul  => 0x20
  | .div  => 0x30
  | .or   => 0x40
  | .and  => 0x50
  | .lsh  => 0x60
  | .rsh  => 0x70
  | .mod  => 0x90
  | .xor  => 0xa0
  | .mov  => 0xb0
  | .arsh => 0xc0

private def jmpBaseOpc : JmpCond → UInt8
  | .eq  => 0x10
  | .gt  => 0x20
  | .ge  => 0x30
  | .set => 0x40
  | .ne  => 0x50
  | .sgt => 0x60
  | .sge => 0x70
  | .lt  => 0xa0
  | .le  => 0xb0
  | .slt => 0xc0
  | .sle => 0xd0

/-! ### Exact Solana sBPF v3 Opcode Tables (SIMD-0178 + SIMD-0189 + SIMD-0377) -/

def ldxOpc : MemSize → UInt8
  | .b1 => 0x71
  | .b2 => 0x69
  | .b4 => 0x61
  | .b8 => 0x79

def stxOpc : MemSize → UInt8
  | .b1 => 0x73
  | .b2 => 0x6b
  | .b4 => 0x63
  | .b8 => 0x7b

def stImmOpc : MemSize → UInt8
  | .b1 => 0x72
  | .b2 => 0x6a
  | .b4 => 0x62
  | .b8 => 0x7a

def alu64RegOpc (op : AluOp) : UInt8 :=
  aluBaseOpc op ||| 0x0f -- BPF_ALU64 | BPF_X

def alu64ImmOpc (op : AluOp) : UInt8 :=
  aluBaseOpc op ||| 0x07 -- BPF_ALU64 | BPF_K

def alu32RegOpc (op : AluOp) : UInt8 :=
  aluBaseOpc op ||| 0x0c -- BPF_ALU32 | BPF_X

def alu32ImmOpc (op : AluOp) : UInt8 :=
  aluBaseOpc op ||| 0x04 -- BPF_ALU32 | BPF_K

/-- Opcode for unary 64-bit negation (`dst = -dst`): `0x87` (`NEG64`). -/
def neg64Opc : UInt8 := 0x87

/-! ### Murmur3-32 Hasher (exact match to Solana `ebpf::hash_symbol_name`) -/

private def rotl32 (x : UInt32) (r : UInt32) : UInt32 :=
  (x <<< r) ||| (x >>> (32 - r))

/-- Exact Murmur3-32 (seed = 0) matching Solana `solana_sbpf::ebpf::hash_symbol_name`. -/
def murmur3_32 (bytes : ByteArray) : UInt32 := Id.run do
  let len := bytes.size
  let nblocks := len / 4
  let c1 : UInt32 := 0xcc9e2d51
  let c2 : UInt32 := 0x1b873593
  let mut h1 : UInt32 := 0
  for i in [0:nblocks] do
    let b := i * 4
    let k0 := (bytes.get! b).toUInt32
    let k1 := (bytes.get! (b + 1)).toUInt32 <<< 8
    let k2 := (bytes.get! (b + 2)).toUInt32 <<< 16
    let k3 := (bytes.get! (b + 3)).toUInt32 <<< 24
    let mut k := k0 ||| k1 ||| k2 ||| k3
    k := k * c1
    k := rotl32 k 15
    k := k * c2
    h1 := h1 ^^^ k
    h1 := rotl32 h1 13
    h1 := h1 * 5 + 0xe6546b64
  let tail := nblocks * 4
  let rem := len - tail
  let mut k1 : UInt32 := 0
  if rem >= 3 then k1 := k1 ^^^ ((bytes.get! (tail + 2)).toUInt32 <<< 16)
  if rem >= 2 then k1 := k1 ^^^ ((bytes.get! (tail + 1)).toUInt32 <<< 8)
  if rem >= 1 then
    k1 := k1 ^^^ (bytes.get! tail).toUInt32
    k1 := k1 * c1
    k1 := rotl32 k1 15
    k1 := k1 * c2
    h1 := h1 ^^^ k1
  h1 := h1 ^^^ len.toUInt32
  h1 := h1 ^^^ (h1 >>> 16)
  h1 := h1 * 0x85ebca6b
  h1 := h1 ^^^ (h1 >>> 13)
  h1 := h1 * 0xc2b2ae35
  h1 := h1 ^^^ (h1 >>> 16)
  return h1

def hashSyscallName (name : String) : UInt32 :=
  murmur3_32 name.toUTF8

/-! ### Assembler (2-pass label resolution -> raw sBPF v3 `.text`, zero relocations) -/

/-- Result of assembling a symbolic sBPF v3 instruction list. -/
structure AssembledText where
  bytes     : ByteArray
  insnCount : Nat

/-- Assemble symbolic `Array Insn` into Solana sBPF v3 `.text` bytecode (SIMD-0178 static syscalls,
    0 relocations). `rodataBaseVaddr` is the exact VM virtual address of `.rodata` (`0x8` when
    non-empty so no `.rodata` pointer is ever NULL `0x0`, or `0` when empty). -/
def assemble (insns : Array Insn) (rodataBaseVaddr : UInt64 := 0) :
    Except String AssembledText := do
  -- Pass 1: record PC (in 8-byte instruction slots) of each label
  let mut labelPc : List (String × Nat) := []
  let mut pc : Nat := 0
  for insn in insns do
    match insn with
    | .label name => labelPc := (name, pc) :: labelPc
    | _ => pc := pc + insn.slotCount
  let findLabel (name : String) : Except String Nat :=
    match labelPc.find? (fun p => p.1 == name) with
    | some (_, targetPc) => .ok targetPc
    | none => .error s!"undefined sBPF label: {name}"
  -- Pass 2: encode every instruction
  let mut buf := ByteArray.emptyWithCapacity (pc * 8)
  let mut curPc : Nat := 0
  for insn in insns do
    match insn with
    | .label _ => pure ()
    | .alu64Reg op dst src =>
      buf := pushRawInsn buf (alu64RegOpc op) dst.idx src.idx 0 0
      curPc := curPc + 1
    | .alu64Imm op dst imm =>
      buf := pushRawInsn buf (alu64ImmOpc op) dst.idx 0 0 imm.toUInt32
      curPc := curPc + 1
    | .alu32Reg op dst src =>
      buf := pushRawInsn buf (alu32RegOpc op) dst.idx src.idx 0 0
      curPc := curPc + 1
    | .alu32Imm op dst imm =>
      buf := pushRawInsn buf (alu32ImmOpc op) dst.idx 0 0 imm.toUInt32
      curPc := curPc + 1
    | .neg64 dst =>
      buf := pushRawInsn buf neg64Opc dst.idx 0 0 0
      curPc := curPc + 1
    | .lddw dst imm =>
      let lo := imm.toUInt32
      let hi := (imm >>> 32).toUInt32
      buf := pushRawInsn buf 0x18 dst.idx 0 0 lo
      buf := pushRawInsn buf 0x00 0 0 0 hi
      curPc := curPc + 2
    | .lddwRodata dst roOff =>
      let va := rodataBaseVaddr + roOff.toUInt64
      let lo := va.toUInt32
      let hi := (va >>> 32).toUInt32
      buf := pushRawInsn buf 0x18 dst.idx 0 0 lo
      buf := pushRawInsn buf 0x00 0 0 0 hi
      curPc := curPc + 2
    | .ldx sz dst src off =>
      buf := pushRawInsn buf (ldxOpc sz) dst.idx src.idx off 0
      curPc := curPc + 1
    | .stx sz dst src off =>
      buf := pushRawInsn buf (stxOpc sz) dst.idx src.idx off 0
      curPc := curPc + 1
    | .stImm sz dst off imm =>
      buf := pushRawInsn buf (stImmOpc sz) dst.idx 0 off imm.toUInt32
      curPc := curPc + 1
    | .ja target =>
      let tPc ← findLabel target
      let delta : Int := (tPc : Int) - ((curPc + 1 : Nat) : Int)
      if delta < -32768 || delta > 32767 then
        throw s!"jump offset out of Int16 range for label {target}: {delta}"
      buf := pushRawInsn buf 0x05 0 0 (Int16.ofInt delta) 0
      curPc := curPc + 1
    | .jccReg cond dst src target =>
      let tPc ← findLabel target
      let delta : Int := (tPc : Int) - ((curPc + 1 : Nat) : Int)
      if delta < -32768 || delta > 32767 then
        throw s!"branch offset out of Int16 range for label {target}: {delta}"
      let opc := jmpBaseOpc cond ||| 0x0d -- BPF_JMP | BPF_X
      buf := pushRawInsn buf opc dst.idx src.idx (Int16.ofInt delta) 0
      curPc := curPc + 1
    | .jccImm cond dst imm target =>
      let tPc ← findLabel target
      let delta : Int := (tPc : Int) - ((curPc + 1 : Nat) : Int)
      if delta < -32768 || delta > 32767 then
        throw s!"branch offset out of Int16 range for label {target}: {delta}"
      let opc := jmpBaseOpc cond ||| 0x05 -- BPF_JMP | BPF_K
      buf := pushRawInsn buf opc dst.idx 0 (Int16.ofInt delta) imm.toUInt32
      curPc := curPc + 1
    | .callLocal target =>
      let tPc ← findLabel target
      let delta : Int := (tPc : Int) - ((curPc + 1 : Nat) : Int)
      if delta == -1 then
        throw s!"invalid self-call (delta = -1) to label {target}"
      -- sBPF v3 (SIMD-0178): CALL_IMM (0x85) with src=1 is a PC-relative internal call
      buf := pushRawInsn buf 0x85 0 1 0 (Int32.ofInt delta).toUInt32
      curPc := curPc + 1
    | .callSyscall symName =>
      -- sBPF v3 (SIMD-0178): CALL_IMM (0x85) with src=0, imm=murmur3_32(symName) (0 relocations!)
      let h := hashSyscallName symName
      buf := pushRawInsn buf 0x85 0 0 0 h
      curPc := curPc + 1
    | .exit =>
      buf := pushRawInsn buf 0x95 0 0 0 0
      curPc := curPc + 1
  return { bytes := buf, insnCount := curPc }

/-! ### Built-In sBPF Disassembler -/

private def aluMnemonic : AluOp → String
  | .add  => "add"
  | .sub  => "sub"
  | .mul  => "mul"
  | .div  => "div"
  | .or   => "or"
  | .and  => "and"
  | .lsh  => "lsh"
  | .rsh  => "rsh"
  | .mod  => "mod"
  | .xor  => "xor"
  | .mov  => "mov"
  | .arsh => "arsh"

private def szSuffix : MemSize → String
  | .b1 => "b"
  | .b2 => "h"
  | .b4 => "w"
  | .b8 => "dw"

private def fmtOff (off : Int16) : String :=
  let i := off.toInt
  if i >= 0 then s!"+{i}" else s!"{i}"

def formatInsn : Insn → String
  | .label name             => s!"{name}:"
  | .alu64Reg op d s        => s!"  {aluMnemonic op}64 {d}, {s}"
  | .alu64Imm op d imm      => s!"  {aluMnemonic op}64 {d}, {imm}"
  | .alu32Reg op d s        => s!"  {aluMnemonic op}32 {d}, {s}"
  | .alu32Imm op d imm      => s!"  {aluMnemonic op}32 {d}, {imm}"
  | .neg64 d                => s!"  neg64 {d}"
  | .lddw d imm             => s!"  lddw {d}, 0x{String.ofList (Nat.toDigits 16 imm.toNat)}"
  | .lddwRodata d off       => s!"  lddw {d}, .rodata+{off}"
  | .ldx sz d s off         => s!"  ldx{szSuffix sz} {d}, [{s}{fmtOff off}]"
  | .stx sz d s off         => s!"  stx{szSuffix sz} [{d}{fmtOff off}], {s}"
  | .stImm sz d off imm     => s!"  st{szSuffix sz} [{d}{fmtOff off}], {imm}"
  | .ja tgt                 => s!"  ja {tgt}"
  | .jccReg c d s tgt       => s!"  {c.mnemonic} {d}, {s}, {tgt}"
  | .jccImm c d imm tgt     => s!"  {c.mnemonic} {d}, {imm}, {tgt}"
  | .callLocal tgt          => s!"  call {tgt}"
  | .callSyscall sym        => s!"  syscall {sym}"
  | .exit                   => "  exit"

def formatProgram (insns : Array Insn) : String :=
  String.intercalate "\n" (insns.toList.map formatInsn)

/-! ### Clean-Room Assembler Slot & Byte-Size Soundness (0 `sorry`, 0 custom axioms) -/

theorem pushRawInsn_size (buf : ByteArray) (opc dst src : UInt8) (off : Int16) (imm : UInt32) :
    (pushRawInsn buf opc dst src off imm).size = buf.size + 8 := by
  simp only [pushRawInsn, pushU16LE, pushU32LE, ByteArray.size_push]

private theorem except_bind_ok {α β ε : Type} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem list_forIn_except_inv {α σ ε : Type}
    (xs : List α) (w : α → Nat) (body : α → σ → Except ε (ForInStep σ)) (Inv : Nat → σ → Prop)
    (hStep : ∀ x k s step, Inv k s → body x s = .ok step →
      ∃ s', step = .yield s' ∧ Inv (k + w x) s') :
    ∀ k s out, Inv k s → forIn xs s body = .ok out → Inv (k + (xs.map w).sum) out := by
  induction xs with
  | nil =>
    intro k s out hI h
    change Except.ok s = Except.ok out at h
    cases h
    simpa using hI
  | cons x tl ih =>
    intro k s out hI h
    rw [List.forIn_cons] at h
    obtain ⟨step, hB, hRest⟩ := except_bind_ok h
    obtain ⟨s', rfl, hI'⟩ := hStep x k s step hI hB
    simpa [Nat.add_assoc] using ih (k + w x) s' out hI' hRest

/-- Every successful sBPF v3 assembly emits exact `insnCount = ∑ Insn.slotCount`
    and `bytes.size = 8 * insnCount` (zero Pass-1/Pass-2 PC drift or byte-alignment skew!). -/
theorem assemble_slot_and_byte_size (insns : Array Insn) (rodataBaseVaddr : UInt64)
    (out : AssembledText) (h : assemble insns rodataBaseVaddr = .ok out) :
    out.insnCount = (insns.toList.map Insn.slotCount).sum ∧
    out.bytes.size = 8 * out.insnCount := by
  unfold assemble at h
  obtain ⟨_, _, h⟩ := except_bind_ok h
  obtain ⟨st, hLoop, hRet⟩ := except_bind_ok h
  cases hRet
  rw [← Array.forIn_toList] at hLoop
  let Inv : Nat → ByteArray × Nat → Prop :=
    fun k s => s.2 = k ∧ s.1.size = 8 * s.2
  have hFinal : Inv (0 + (insns.toList.map Insn.slotCount).sum) st := by
    refine list_forIn_except_inv insns.toList Insn.slotCount _ Inv ?_ 0 _ st ⟨rfl, rfl⟩ hLoop
    intro insn k s step ⟨hk, hb⟩ hB
    cases insn <;> dsimp only [Insn.slotCount] at hB ⊢
    all_goals
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe] at hB
      repeat' split at hB
      all_goals cases hB
      all_goals
        refine ⟨_, rfl, ?_⟩
        simp only [Inv, pushRawInsn_size]
        constructor <;> omega
  simpa [Inv] using hFinal

end LeanSVM.SBPF
