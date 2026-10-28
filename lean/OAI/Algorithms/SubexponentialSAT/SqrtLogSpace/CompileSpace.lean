import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.GuardedCompiler

/-! Transfer a genuine bound on every source stack configuration through the
guarded primitive compiler. The bound is independent of the number of source
instructions. Concrete counting programs must prove the source invariant. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace

open GuardedCompiler
open scoped BigOperators

private theorem compile_trace_envelope {r s l : ℕ} (p : BitProgram.Program r s l)
    (anchor : Fin s → ℤ) (bound inputLength : ℕ)
    (hanchor : ∀ i, 0 ≤ anchor i ∧ anchor i ≤ (inputLength : ℤ))
    {a b : BitProgram.Cfg r s l} {sourceSteps : ℕ}
    (tr : BitProgram.Trace p sourceSteps a b) {c : LocatedCfg (primitive p)}
    (hcfg : c.config = primitiveCfg p a)
    (hposition : ∀ i, c.position i = anchor i - ((a.stacks i).length : ℤ))
    (henvelope : ∀ i, -(bound : ℤ) - 7 ≤ c.lower i ∧
      c.upper i ≤ (inputLength : ℤ) + 7)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps a intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time c d ∧
      d.config = primitiveCfg p b ∧
      (∀ i, d.position i = anchor i - ((b.stacks i).length : ℤ)) ∧
      ∀ i, -(bound : ℤ) - 7 ≤ d.lower i ∧
        d.upper i ≤ (inputLength : ℤ) + 7 := by
  induction tr generalizing c with
  | refl => exact ⟨0, by omega, c, .refl c, hcfg, hposition, henvelope⟩
  | @cons sourceSteps a next final hs ht ih =>
      obtain ⟨time₁, htime₁, middle, hrun₁, hcfg₁, hshift⟩ :=
        primitive_located_step p hs hcfg
      have hposition₁ : ∀ i,
          middle.position i = anchor i - ((next.stacks i).length : ℤ) := by
        intro i
        rw [hshift i, hposition i]
        omega
      have henvelope₁ : ∀ i, -(bound : ℤ) - 7 ≤ middle.lower i ∧
          middle.upper i ≤ (inputLength : ℤ) + 7 := by
        apply locatedTrace_envelope_of_margin hrun₁ htime₁
          (fun _ => -(bound : ℤ) - 7) (fun _ => (inputLength : ℤ) + 7) henvelope
        intro i
        have hlength := hstacks 0 a (by omega) (.refl a) i
        have ha := hanchor i
        rw [hposition i]
        omega
      have hstacks₁ : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
          BitProgram.Trace p prefixSteps next intermediate →
          ∀ i, (intermediate.stacks i).length ≤ bound := by
        intro prefixSteps intermediate hle htrace
        exact hstacks (prefixSteps + 1) intermediate (by omega) (.cons hs htrace)
      obtain ⟨time₂, htime₂, d, hrun₂, hcfg₂, hposition₂, henvelope₂⟩ :=
        ih hcfg₁ hposition₁ henvelope₁ hstacks₁
      exact ⟨time₁ + time₂, by omega, d, hrun₁.trans hrun₂,
        hcfg₂, hposition₂, henvelope₂⟩

theorem compile_trace_space {r s l : ℕ} (p : BitProgram.Program r s l)
    {input : List Bool} {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time
        (locatedInit (primitive p) input) d ∧
      d.config = primitiveCfg p final ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (primitive p)) prefixSteps
          (locatedInit (primitive p) input) intermediate →
        visitedSpace intermediate ≤ s * (bound + input.length + 15) := by
  let anchor : Fin s → ℤ := fun i => if i = p.inputStack then input.length else 0
  have hanchor : ∀ i, 0 ≤ anchor i ∧ anchor i ≤ (input.length : ℤ) := by
    intro i
    dsimp [anchor]
    split_ifs <;> omega
  have hposition : ∀ i : Fin s, (locatedInit (primitive p) input).position i =
      anchor i - (((BitProgram.initial p input).stacks i).length : ℤ) := by
    intro i
    by_cases hi : i = p.inputStack <;> simp [locatedInit, anchor, hi]
  have henvelope : ∀ i, -(bound : ℤ) - 7 ≤ (locatedInit (primitive p) input).lower i ∧
      (locatedInit (primitive p) input).upper i ≤ (input.length : ℤ) + 7 := by
    intro i
    simp only [locatedInit, Int.ofNat_eq_natCast]
    split_ifs <;> omega
  obtain ⟨time, htime, d, hrun, hcfg, _, hspace⟩ :=
    compile_trace_envelope p anchor bound input.length hanchor tr
      (primitive_initial p input).symm hposition henvelope hstacks
  refine ⟨time, htime, d, hrun, hcfg, ?_⟩
  intro prefixSteps intermediate hle hprefix
  apply (locatedTrace_prefix_space hrun hprefix hle).trans
  apply (visitedSpace_le_of_envelope d _ _ hspace).trans
  have hwidth : ((input.length : ℤ) + 7 - (-(bound : ℤ) - 7) + 1).toNat =
      bound + input.length + 15 := by omega
  simp only [hwidth, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
  exact le_rfl

/-- Full output-word readback, time, and every-prefix visited space refer to
one and the same primitive execution. The actual source trace and source-stack
invariant must be provided by the concrete counting program. -/
theorem compile_word_space {r s l : ℕ} (p : BitProgram.Program r s l)
    {input output : List Bool} {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hout : final.stacks p.outputStack = output)
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time
        (locatedInit (primitive p) input) d ∧
      d.config.state = .inl (output.head?.getD false) ∧
      d.config.tapes p.outputStack = Turing.Tape.mk₁ (output.map some) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (primitive p)) prefixSteps
          (locatedInit (primitive p) input) intermediate →
        visitedSpace intermediate ≤ s * (bound + input.length + 15) := by
  obtain ⟨time, htime, d, hrun, hcfg, hspace⟩ := compile_trace_space p tr hstacks
  refine ⟨time, htime, d, hrun, ?_, ?_, hspace⟩
  · rw [hcfg, primitive_halted p final halted, hout]
  · rw [hcfg, primitive_tape, hout]

/-- A full word on an arbitrary fixed tape and a separate Boolean halt are
preserved by the same execution used for both resource bounds. -/
theorem compile_word_answer_space {r s l : ℕ} (p : BitProgram.Program r s l)
    (countStack : Fin s) {input word : List Bool} {answer : Bool}
    {final : BitProgram.Cfg r s l} {sourceSteps bound : ℕ}
    (tr : BitProgram.Trace p sourceSteps (BitProgram.initial p input) final)
    (halted : final.pc = none) (hword : final.stacks countStack = word)
    (hanswer : final.stacks p.outputStack = [answer])
    (hstacks : ∀ prefixSteps intermediate, prefixSteps ≤ sourceSteps →
      BitProgram.Trace p prefixSteps (BitProgram.initial p input) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∃ time ≤ 7 * sourceSteps, ∃ d : LocatedCfg (primitive p),
      Computation.Trace (locatedStep (primitive p)) time
        (locatedInit (primitive p) input) d ∧
      d.config.state = .inl answer ∧
      d.config.tapes countStack = Turing.Tape.mk₁ (word.map some) ∧
      d.config.tapes p.outputStack = Turing.Tape.mk₁ [some answer] ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace (locatedStep (primitive p)) prefixSteps
          (locatedInit (primitive p) input) intermediate →
        visitedSpace intermediate ≤ s * (bound + input.length + 15) := by
  obtain ⟨time, htime, d, hrun, hcfg, hspace⟩ := compile_trace_space p tr hstacks
  refine ⟨time, htime, d, hrun, ?_, ?_, ?_, hspace⟩
  · rw [hcfg, primitive_halted p final halted, hanswer]
    rfl
  · rw [hcfg, primitive_tape, hword]
  · rw [hcfg, primitive_tape, hanswer]
    rfl

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CompileSpace
