import LeanSVM.SBPF.ISA

namespace LeanSVM.SBPF

/-- Encoding a raw instruction appends exactly one slot to any existing text. -/
theorem size_pushRawInsn (buf : ByteArray) (opc dst src : UInt8) (off : Int16) (imm : UInt32) :
    (pushRawInsn buf opc dst src off imm).size = buf.size + 8 := by
  simp only [pushRawInsn, pushU16LE, pushU32LE, ByteArray.size_push]

private theorem bind_ok {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A successful sequence of yields accumulates the sum of its input weights. -/
private theorem forIn_slots (xs : List α) (weight : α → Nat)
    (step : α → σ → Except ε (ForInStep σ)) (P : Nat → σ → Prop)
    (advance : ∀ x n s t, P n s → step x s = .ok t →
      ∃ s', t = .yield s' ∧ P (n + weight x) s') :
    ∀ n s out, P n s → forIn xs s step = .ok out → P (n + (xs.map weight).sum) out := by
  induction xs with
  | nil =>
    intro n s out hs h
    change Except.ok s = Except.ok out at h
    cases h
    simpa using hs
  | cons x xs ih =>
    intro n s out hs h
    rw [List.forIn_cons] at h
    obtain ⟨t, ht, htail⟩ := bind_ok h
    obtain ⟨s', rfl, hs'⟩ := advance x n s t hs ht
    simpa [Nat.add_assoc] using ih _ s' out hs' htail

/-- The assembler's slot count agrees with the symbolic layout, and its text
    contains exactly eight bytes per slot, for every successful assembly. -/
theorem assemble_layout {insns : Array Insn} {ver : Version} {base : UInt64}
    {out : AssembledText} (h : assemble insns ver base = .ok out) :
    out.insnCount = (insns.toList.map (Insn.slotCount ver)).sum ∧
    out.bytes.size = 8 * out.insnCount := by
  unfold assemble at h
  -- The label pass may supply any table and allocation hint to the emitter.
  obtain ⟨labels, _, h⟩ := bind_ok h
  obtain ⟨s, hloop, hout⟩ := bind_ok h
  cases hout
  rw [← Array.forIn_toList] at hloop
  let layout := fun (n : Nat) (s : ByteArray × Array SyscallReloc × Array RodataFixup × Nat) =>
    s.2.2.2 = n ∧ s.1.size = 8 * s.2.2.2
  change layout _ s
  rw [← Nat.zero_add (insns.toList.map _).sum]
  refine forIn_slots _ (Insn.slotCount ver) _ layout (n := 0) (s := _) (out := s) ?_ ?_ hloop
  · intro x n st t hst hx
    obtain ⟨hn, hb⟩ := hst
    clear hloop
    -- Errors cannot yield a next state. On success, count the actual raw writes.
    cases x <;> dsimp only [Insn.slotCount] at hx ⊢
    all_goals
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe] at hx
      repeat' split at hx
      all_goals cases hx
      all_goals
        refine ⟨_, rfl, ?_⟩
        simp only [layout, size_pushRawInsn]
        constructor <;> omega
  · exact ⟨rfl, rfl⟩

/-- Size of a successful assembly, computed solely from the symbolic program. -/
theorem assemble_bytes_size {insns : Array Insn} {ver : Version} {base : UInt64}
    {out : AssembledText} (h : assemble insns ver base = .ok out) :
    out.bytes.size = 8 * (insns.toList.map (Insn.slotCount ver)).sum := by
  obtain ⟨hslots, hbytes⟩ := assemble_layout h
  rw [hbytes, hslots]

-- A forward jump over both kinds of wide instruction lands at a zero-width label.
example (ver : Version) :
    (assemble #[.ja "end", .lddw Reg.r1 42, .lddwRodata Reg.r2 0, .label "end", .exit] ver).map
      (fun out => (out.insnCount, out.bytes.size)) = .ok (6, 48) := by
  cases ver <;> rfl

end LeanSVM.SBPF
