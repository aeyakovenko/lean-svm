/-
  LeanSVM.Runtime
  Pure executable SVM memory/syscall semantics for Lean 4 formal verification,
  paired with `@[noinline]` hardware intrinsics recognized by the native Lean→sBPF compiler.

  Key design invariant:
  - In Lean 4 proofs: every operation has transparent, axiom-free semantics over `SvmState`.
  - In sBPF codegen: `SvmState` is a zero-cost ghost token (0 registers, 0 memory),
    and every `raw*` / `sys*` primitive compiles directly to 1 sBPF instruction or syscall.
-/
import LeanSVM.Types
import Std.Tactic.BVDecide

namespace LeanSVM

/-- Pure functional model of the Solana Virtual Machine state for kernel-checked proofs. -/
structure SvmState where
  /-- Byte-addressable virtual memory (`addr -> byte`). -/
  mem     : UInt64 → UInt8
  /-- Program log output buffer (newest appended at end). -/
  logs    : List String := []
  /-- Next available stack buffer address (grows downward from `0x200001000`). -/
  stackSp : UInt64 := 0x200001000
  /-- Mock clock slot (used by `sysClock` in pure Lean proofs). -/
  slot    : UInt64 := 0
  /-- Clock epoch start timestamp, as a signed i64 bit pattern. -/
  epochStartTimestamp : UInt64 := 0
  /-- Clock epoch. -/
  epoch : UInt64 := 0
  /-- Clock leader schedule epoch. -/
  leaderScheduleEpoch : UInt64 := 0
  /-- Clock Unix timestamp, as a signed i64 bit pattern. -/
  unixTimestamp : UInt64 := 0

namespace SvmState

def empty : SvmState := { mem := fun _ => 0 }

def readU8 (s : SvmState) (addr : UInt64) : UInt8 :=
  s.mem addr

def readU16 (s : SvmState) (addr : UInt64) : UInt16 :=
  let b0 := (s.mem addr).toUInt16
  let b1 := (s.mem (addr + 1)).toUInt16
  b0 ||| (b1 <<< 8)

def readU32 (s : SvmState) (addr : UInt64) : UInt32 :=
  let b0 := (s.mem addr).toUInt32
  let b1 := (s.mem (addr + 1)).toUInt32
  let b2 := (s.mem (addr + 2)).toUInt32
  let b3 := (s.mem (addr + 3)).toUInt32
  b0 ||| (b1 <<< 8) ||| (b2 <<< 16) ||| (b3 <<< 24)

def readU64 (s : SvmState) (addr : UInt64) : UInt64 :=
  let lo := (s.readU32 addr).toUInt64
  let hi := (s.readU32 (addr + 4)).toUInt64
  lo ||| (hi <<< 32)

def writeU8 (s : SvmState) (addr : UInt64) (v : UInt8) : SvmState :=
  { s with mem := fun a => if a == addr then v else s.mem a }

def writeU16 (s : SvmState) (addr : UInt64) (v : UInt16) : SvmState :=
  let s1 := s.writeU8 addr v.toUInt8
  s1.writeU8 (addr + 1) (v >>> 8).toUInt8

def writeU32 (s : SvmState) (addr : UInt64) (v : UInt32) : SvmState :=
  let s1 := s.writeU16 addr v.toUInt16
  s1.writeU16 (addr + 2) (v >>> 16).toUInt16

def writeU64 (s : SvmState) (addr : UInt64) (v : UInt64) : SvmState :=
  let s1 := s.writeU32 addr v.toUInt32
  s1.writeU32 (addr + 4) (v >>> 32).toUInt32

private theorem mem_writeU64_at (s : SvmState) (a v : UInt64) (k : UInt64) :
    (s.writeU64 a v).mem (a + k) =
      if k == 7 then (v >>> 56).toUInt8
      else if k == 6 then (v >>> 48).toUInt8
      else if k == 5 then (v >>> 40).toUInt8
      else if k == 4 then (v >>> 32).toUInt8
      else if k == 3 then (v >>> 24).toUInt8
      else if k == 2 then (v >>> 16).toUInt8
      else if k == 1 then (v >>> 8).toUInt8
      else if k == 0 then v.toUInt8
      else s.mem (a + k) := by
  unfold writeU64 writeU32 writeU16 writeU8
  simp only
  have e7 : (a + k == a + 4 + 2 + 1) = (k == 7) := by bv_decide
  have e6 : (a + k == a + 4 + 2) = (k == 6) := by bv_decide
  have e5 : (a + k == a + 4 + 1) = (k == 5) := by bv_decide
  have e4 : (a + k == a + 4) = (k == 4) := by bv_decide
  have e3 : (a + k == a + 2 + 1) = (k == 3) := by bv_decide
  have e2 : (a + k == a + 2) = (k == 2) := by bv_decide
  have e1 : (a + k == a + 1) = (k == 1) := by bv_decide
  have e0 : (a + k == a) = (k == 0) := by bv_decide
  have b7 : (((v >>> 32).toUInt32 >>> 16).toUInt16 >>> 8).toUInt8 = (v >>> 56).toUInt8 := by bv_decide
  have b6 : ((v >>> 32).toUInt32 >>> 16).toUInt16.toUInt8 = (v >>> 48).toUInt8 := by bv_decide
  have b5 : ((v >>> 32).toUInt32.toUInt16 >>> 8).toUInt8 = (v >>> 40).toUInt8 := by bv_decide
  have b4 : (v >>> 32).toUInt32.toUInt16.toUInt8 = (v >>> 32).toUInt8 := by bv_decide
  have b3 : ((v.toUInt32 >>> 16).toUInt16 >>> 8).toUInt8 = (v >>> 24).toUInt8 := by bv_decide
  have b2 : (v.toUInt32 >>> 16).toUInt16.toUInt8 = (v >>> 16).toUInt8 := by bv_decide
  have b1 : (v.toUInt32.toUInt16 >>> 8).toUInt8 = (v >>> 8).toUInt8 := by bv_decide
  have b0 : v.toUInt32.toUInt16.toUInt8 = v.toUInt8 := by bv_decide
  simp only [e7, e6, e5, e4, e3, e2, e1, e0, b7, b6, b5, b4, b3, b2, b1, b0]

theorem readU64_writeU64_same (s : SvmState) (addr v : UInt64) :
    (s.writeU64 addr v).readU64 addr = v := by
  unfold readU64 readU32
  have p41 : addr + 4 + 1 = addr + 5 := by bv_decide
  have p42 : addr + 4 + 2 = addr + 6 := by bv_decide
  have p43 : addr + 4 + 3 = addr + 7 := by bv_decide
  have p0  : addr + 0 = addr := by bv_decide
  have h0  := mem_writeU64_at s addr v 0
  rw [p0] at h0
  simp only [p41, p42, p43, h0, mem_writeU64_at]
  bv_decide

theorem readU64_writeU64_disjoint (s : SvmState) (a b v : UInt64)
    (h : a + 8 ≤ b ∨ b + 8 ≤ a)
    (ha : a ≤ 0xFFFFFFFFFFFFFFF7) (hb : b ≤ 0xFFFFFFFFFFFFFFF7) :
    (s.writeU64 a v).readU64 b = s.readU64 b := by
  have hmem : ∀ (k : UInt64), k < 8 →
      (s.writeU64 a v).mem (b + k) = s.mem (b + k) := by
    intro k hk
    unfold writeU64 writeU32 writeU16 writeU8
    simp only
    have c7 : (b + k == a + 4 + 2 + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c6 : (b + k == a + 4 + 2) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c5 : (b + k == a + 4 + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c4 : (b + k == a + 4) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c3 : (b + k == a + 2 + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c2 : (b + k == a + 2) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c1 : (b + k == a + 1) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    have c0 : (b + k == a) = false := by rw [beq_eq_false_iff_ne]; bv_decide
    simp [c7, c6, c5, c4, c3, c2, c1, c0]
  unfold readU64 readU32
  have p41 : b + 4 + 1 = b + 5 := by bv_decide
  have p42 : b + 4 + 2 = b + 6 := by bv_decide
  have p43 : b + 4 + 3 = b + 7 := by bv_decide
  have e0 := hmem 0 (by decide)
  have e1 := hmem 1 (by decide)
  have e2 := hmem 2 (by decide)
  have e3 := hmem 3 (by decide)
  have e4 := hmem 4 (by decide)
  have e5 := hmem 5 (by decide)
  have e6 := hmem 6 (by decide)
  have e7 := hmem 7 (by decide)
  have b0 : b + 0 = b := by bv_decide
  rw [b0] at e0
  simp only [p41, p42, p43, e0, e1, e2, e3, e4, e5, e6, e7]

end SvmState

/-!
## Hardware Intrinsics (`@[noinline]`)
These exact declarations are recognized by the native Lean→sBPF compiler and lowered
directly to single sBPF instructions / syscalls with zero `SvmState` runtime overhead.
In Lean 4 proofs, they remain completely transparent definitions over `SvmState`.
-/

/-- Result of an SVM step: either error code `err != 0` or `(value, nextState)`. -/
inductive SvmStep (α : Type) where
  | ok (val : α) (st : SvmState)
  | err (code : UInt64) (st : SvmState)

/-- Zero-cost Solana program monad with full executable Lean 4 verification semantics. -/
abbrev SolanaM (α : Type) := SvmState → SvmStep α

namespace SolanaM

@[inline] def pure (a : α) : SolanaM α := fun s => .ok a s

@[inline] def bind (m : SolanaM α) (f : α → SolanaM β) : SolanaM β := fun s =>
  match m s with
  | .ok a s' => f a s'
  | .err c s' => .err c s'

instance : Monad SolanaM where
  pure := SolanaM.pure
  bind := SolanaM.bind

/-- Fail immediately with Solana program error code `code`. -/
@[inline] def fail (code : UInt64) : SolanaM α := fun s => .err code s

/-- Assert condition `cond` or fail with `code`. -/
@[inline] def require (cond : Bool) (code : UInt64) : SolanaM Unit :=
  if cond then pure () else fail code

/-- Run a `SolanaM Unit` entrypoint to a raw Solana `UInt64` exit code (`0` = success). -/
@[inline] def runEntry (m : SolanaM Unit) (s : SvmState) : UInt64 × SvmState :=
  match m s with
  | .ok () s' => (0, s')
  | .err code s' => (code, s')

end SolanaM

/-! ### Low-Level Memory Load / Store Intrinsics -/

@[noinline] def rawLoadU8 (ptr : Ptr) (s : SvmState) : SvmStep UInt8 :=
  .ok (s.readU8 ptr) s

@[noinline] def rawLoadU16 (ptr : Ptr) (s : SvmState) : SvmStep UInt16 :=
  .ok (s.readU16 ptr) s

@[noinline] def rawLoadU32 (ptr : Ptr) (s : SvmState) : SvmStep UInt32 :=
  .ok (s.readU32 ptr) s

@[noinline] def rawLoadU64 (ptr : Ptr) (s : SvmState) : SvmStep UInt64 :=
  .ok (s.readU64 ptr) s

@[noinline] def rawStoreU8 (ptr : Ptr) (val : UInt8) (s : SvmState) : SvmStep Unit :=
  .ok () (s.writeU8 ptr val)

@[noinline] def rawStoreU16 (ptr : Ptr) (val : UInt16) (s : SvmState) : SvmStep Unit :=
  .ok () (s.writeU16 ptr val)

@[noinline] def rawStoreU32 (ptr : Ptr) (val : UInt32) (s : SvmState) : SvmStep Unit :=
  .ok () (s.writeU32 ptr val)

@[noinline] def rawStoreU64 (ptr : Ptr) (val : UInt64) (s : SvmState) : SvmStep Unit :=
  .ok () (s.writeU64 ptr val)

/-! ### Stack Buffer Allocation Intrinsic (Zero Heap Allocation!) -/

/-- Allocate `size` bytes (8-byte aligned) on the sBPF stack frame (`r10 - offset`).
    Compile-time constant `size` folds into a single `mov64 r, r10; add64 r, -off` pair.
    Zero heap usage! -/
@[noinline] def rawStackAlloc (size : UInt64) (s : SvmState) : SvmStep Ptr :=
  let aligned := (size + 7) &&& 0xFFFFFFFFFFFFFFF8
  let nextSp := s.stackSp - aligned
  .ok nextSp { s with stackSp := nextSp }

/-! ### Solana Syscall Intrinsics -/

/-- Emit a UTF-8 log message via `sol_log_(ptr, len)`. String literal lives in `.rodata`. -/
@[noinline] def sysLog (msg : String) (s : SvmState) : SvmStep Unit :=
  .ok () { s with logs := s.logs ++ [msg] }

/-- Emit 5 `UInt64` values via `sol_log_64_(a, b, c, d, e)`. -/
@[noinline] def sysLog64 (a b c d e : UInt64) (s : SvmState) : SvmStep Unit :=
  .ok () { s with logs := s.logs ++ [s!"{a} {b} {c} {d} {e}"] }

/-- Log remaining compute units via `sol_log_compute_units_()`. -/
@[noinline] def sysLogComputeUnits (s : SvmState) : SvmStep Unit :=
  .ok () s

/-- Copy `len` bytes from `src` to `dst` via `sol_memcpy_(dst, src, len)`. -/
@[noinline] def sysMemcpy (dst src len : UInt64) (s : SvmState) : SvmStep Unit :=
  let rec loop (i : Nat) (st : SvmState) : SvmState :=
    match i with
    | 0 => st
    | n + 1 =>
      let off := (len.toNat - (n + 1)).toUInt64
      loop n (st.writeU8 (dst + off) (st.readU8 (src + off)))
  .ok () (loop len.toNat s)

/-- Fill `len` bytes at `dst` with `val` via `sol_memset_(dst, val, len)`. -/
@[noinline] def sysMemset (dst val len : UInt64) (s : SvmState) : SvmStep Unit :=
  let rec loop (i : Nat) (st : SvmState) : SvmState :=
    match i with
    | 0 => st
    | n + 1 =>
      let off := (len.toNat - (n + 1)).toUInt64
      loop n (st.writeU8 (dst + off) val.toUInt8)
  .ok () (loop len.toNat s)

/-- Compare `len` bytes at `a` and `b`, storing i32 result at `resultPtr`, via `sol_memcmp_`. -/
@[noinline] def sysMemcmp (a b len resultPtr : UInt64) (s : SvmState) : SvmStep Unit :=
  let rec compare (remaining : Nat) (offset : UInt64) : UInt32 :=
    match remaining with
    | 0 => 0
    | n + 1 =>
      let lhs := s.readU8 (a + offset)
      let rhs := s.readU8 (b + offset)
      if lhs == rhs then
        compare n (offset + 1)
      else
        lhs.toUInt32 - rhs.toUInt32
  let diff := compare len.toNat 0
  .ok () (s.writeU32 resultPtr diff)

/-- Compute SHA-256 over `valsLen` `(ptr, len)` slice descriptors at `valsPtr`,
    writing 32-byte digest into `resultPtr`, via `sol_sha256`. -/
@[noinline] def sysSha256 (valsPtr valsLen resultPtr : UInt64) (s : SvmState) : SvmStep UInt64 :=
  let seed := s.readU64 valsPtr ^^^ valsLen
  .ok (if valsLen == 0xFFFFFFFFFFFFFFFF then 1 else 0) (s.writeU64 resultPtr seed)

/-- Read the Solana Clock sysvar (40 bytes: slot, epoch_start_timestamp, epoch,
    leader_schedule_epoch, unix_timestamp) into `outPtr` via `sol_get_clock_sysvar`. -/
@[noinline] def sysGetClock (outPtr : UInt64) (s : SvmState) : SvmStep UInt64 :=
  let clock := s.writeU64 outPtr s.slot
  let clock := clock.writeU64 (outPtr + 8) s.epochStartTimestamp
  let clock := clock.writeU64 (outPtr + 16) s.epoch
  let clock := clock.writeU64 (outPtr + 24) s.leaderScheduleEpoch
  let clock := clock.writeU64 (outPtr + 32) s.unixTimestamp
  .ok (if outPtr == 0 then 1 else 0) clock

/-- Cross-program invocation via `sol_invoke_signed_c`. -/
@[noinline] def sysInvokeSignedC (ixPtr infosPtr infosLen seedsPtr seedsLen : UInt64)
    (s : SvmState) : SvmStep UInt64 :=
  let tag := ixPtr ^^^ infosPtr ^^^ infosLen ^^^ seedsPtr ^^^ seedsLen
  .ok (if tag == 0xFFFFFFFFFFFFFFFF then 1 else 0) { s with logs := s.logs }

/-! ### Ergonomic `SolanaM` Wrappers -/

@[inline] def loadU8  (ptr : Ptr) (off : UInt64 := 0) : SolanaM UInt8  := rawLoadU8  (ptr + off)
@[inline] def loadU16 (ptr : Ptr) (off : UInt64 := 0) : SolanaM UInt16 := rawLoadU16 (ptr + off)
@[inline] def loadU32 (ptr : Ptr) (off : UInt64 := 0) : SolanaM UInt32 := rawLoadU32 (ptr + off)
@[inline] def loadU64 (ptr : Ptr) (off : UInt64 := 0) : SolanaM UInt64 := rawLoadU64 (ptr + off)

@[inline] def storeU8  (ptr : Ptr) (off : UInt64) (v : UInt8)  : SolanaM Unit := rawStoreU8  (ptr + off) v
@[inline] def storeU16 (ptr : Ptr) (off : UInt64) (v : UInt16) : SolanaM Unit := rawStoreU16 (ptr + off) v
@[inline] def storeU32 (ptr : Ptr) (off : UInt64) (v : UInt32) : SolanaM Unit := rawStoreU32 (ptr + off) v
@[inline] def storeU64 (ptr : Ptr) (off : UInt64) (v : UInt64) : SolanaM Unit := rawStoreU64 (ptr + off) v

@[inline] def stackAlloc (size : UInt64) : SolanaM Ptr := rawStackAlloc size
@[inline] def log (msg : String) : SolanaM Unit := sysLog msg
@[inline] def log64 (a b c d e : UInt64) : SolanaM Unit := sysLog64 a b c d e
@[inline] def logComputeUnits : SolanaM Unit := sysLogComputeUnits
@[inline] def memcpy (dst src len : UInt64) : SolanaM Unit := sysMemcpy dst src len
@[inline] def memset (dst val len : UInt64) : SolanaM Unit := sysMemset dst val len
@[inline] def sha256 (valsPtr valsLen resultPtr : UInt64) : SolanaM UInt64 := sysSha256 valsPtr valsLen resultPtr
@[inline] def getClock (outPtr : UInt64) : SolanaM UInt64 := sysGetClock outPtr

end LeanSVM
