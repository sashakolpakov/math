import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchScheduleBounds
import OAI.Algorithms.SubexponentialSAT.QuarticSearch

namespace OAI.Algorithms

/-!
# Scheduled execution on the produced local-basis inputs

The coefficient function is serialized with `List.ofFn`, and the alphabet
has the reversed order returned by the scalar producer. Their lengths and
alphabet completeness are discharged here. The fixed primitive program's
actual run and emitted rows retain the budget `2 ^ scale n` eventually.
-/

namespace SubexponentialSAT.Subexp.LocalBasisBatchScheduleBounds

open Filter SubexpPackingParameters LocalBasisBatchProgram BitProgram

attribute [local instance] scheduledPrime

theorem scheduled_two_ne_zero (n : ℕ) : (2 : ZMod (p n)) ≠ 0 := by
  intro h
  have hd : p n ∣ 2 := (ZMod.natCast_eq_zero_iff 2 (p n)).mp h
  have hp := Nat.le_of_dvd (by decide : 0 < 2) hd
  have ht := p_gt_two n
  omega

theorem eventually_ofFn_sourceBudget_le_scale (k T factor : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (hr : 0 < r n) (hQ : 0 < DyadicSchedule.Q n)
      (coefficients : Fin (DyadicSchedule.R k T n) → ZMod (p n)),
      ((factor * sourceBudget (Δ := DyadicSchedule.delta k T n)
        (p n) hr hQ (List.ofFn coefficients) (QuarticSearch.elements (p n)).reverse : ℕ) : ℝ) ≤
          (2 : ℝ) ^ SubexpComputation.scale n := by
  filter_upwards [eventually_sourceBudget_le_scale k T factor] with n hn
  intro hr hQ coefficients
  exact hn hr hQ (List.ofFn coefficients) (QuarticSearch.elements (p n)).reverse
    (by simp) (by simp)

/-- The actual native trace, successful rows, and emitted byte bound all
come from the fixed program. The multiplier is fixed before the input size. -/
theorem eventually_program_runs (k T factor : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (hr : 0 < r n) (hQ : 0 < DyadicSchedule.Q n)
      (coefficients : Fin (DyadicSchedule.R k T n) → ZMod (p n))
      (regs : Fin 32 → Bool),
      ∃ budget : ℕ, ∃ rows finalRegs,
        ((factor * budget : ℕ) : ℝ) ≤ (2 : ℝ) ^ SubexpComputation.scale n ∧
        (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords)).length ≤ budget ∧
        RowsGood (GoodResult (Δ := DyadicSchedule.delta k T n)
          (p n) hr hQ (List.ofFn coefficients)) (r n) (DyadicSchedule.Q n) rows ∧
        RunsIn program budget
          ((inputState (canonicalContext (p n) (r n) (DyadicSchedule.Q n)
            (DyadicSchedule.delta k T n) (List.ofFn coefficients)
            (QuarticSearch.elements (p n)).reverse) regs).withPC (some program.entry))
          ((outputState (canonicalContext (p n) (r n) (DyadicSchedule.Q n)
            (DyadicSchedule.delta k T n) (List.ofFn coefficients)
            (QuarticSearch.elements (p n)).reverse)
            (TypeIndexProgram.unary (DyadicSchedule.Q n * r n))
            (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords))
            finalRegs).withPC none) := by
  filter_upwards [eventually_ofFn_sourceBudget_le_scale k T factor] with n hn
  intro hr hQ coefficients regs
  have hfull : ∀ x : ZMod (p n), x ∈ (QuarticSearch.elements (p n)).reverse := by
    intro x
    simpa only [List.mem_reverse] using QuarticSearch.mem_elements (p n) x
  obtain ⟨rows, finalRegs, hg, he⟩ := LocalBasisBatchProgram.program_runsIn
    (Δ := DyadicSchedule.delta k T n) (p n) (scheduled_two_ne_zero n)
    hr hQ (List.ofFn coefficients) (QuarticSearch.elements (p n)).reverse hfull regs
  exact ⟨_, rows, finalRegs, hn hr hQ coefficients,
    LocalBasisBatchBounds.output_length_le_of_runsIn _ _ _ regs finalRegs _ he, hg, he⟩

/-- The compiler's fixed overhead is charged. Both endpoints are the actual
encoded native configurations, with the exact output records retained. -/
theorem eventually_primitive_runs (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (hr : 0 < r n) (hQ : 0 < DyadicSchedule.Q n)
      (coefficients : Fin (DyadicSchedule.R k T n) → ZMod (p n))
      (regs : Fin 32 → Bool),
      ∃ budget : ℕ, ∃ rows finalRegs,
        (budget : ℝ) ≤ (2 : ℝ) ^ SubexpComputation.scale n ∧
        RowsGood (GoodResult (Δ := DyadicSchedule.delta k T n)
          (p n) hr hQ (List.ofFn coefficients)) (r n) (DyadicSchedule.Q n) rows ∧
        Computation.RunsIn (primitive program).step budget
          (primitiveCfg program ((inputState
            (canonicalContext (p n) (r n) (DyadicSchedule.Q n)
              (DyadicSchedule.delta k T n) (List.ofFn coefficients)
              (QuarticSearch.elements (p n)).reverse) regs).withPC (some program.entry)))
          (primitiveCfg program ((outputState
            (canonicalContext (p n) (r n) (DyadicSchedule.Q n)
              (DyadicSchedule.delta k T n) (List.ofFn coefficients)
              (QuarticSearch.elements (p n)).reverse)
            (TypeIndexProgram.unary (DyadicSchedule.Q n * r n))
            (ProgramEncoding.encodeRecords (rows.map ProgramEncoding.encodeRecords))
            finalRegs).withPC none)) := by
  filter_upwards [eventually_program_runs k T (primitiveOverhead program)] with n hn
  intro hr hQ coefficients regs
  obtain ⟨budget, rows, finalRegs, hb, _, hg, he⟩ := hn hr hQ coefficients regs
  exact ⟨primitiveOverhead program * budget, rows, finalRegs,
    hb, hg, primitive_execution program he⟩

theorem eventually_ofFn_input_bits_le_scale (k T : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (coefficients : Fin (DyadicSchedule.R k T n) → ZMod (p n))
        (regs : Fin 32 → Bool),
      (stackBits (inputState (canonicalContext (p n) (r n) (DyadicSchedule.Q n)
        (DyadicSchedule.delta k T n) (List.ofFn coefficients)
        (QuarticSearch.elements (p n)).reverse) regs).stacks : ℝ) ≤
          SubexpComputation.scale n := by
  filter_upwards [eventually_input_bits_le_scale k T] with n hn
  intro coefficients regs
  exact hn (List.ofFn coefficients) (QuarticSearch.elements (p n)).reverse
    (by simp) (by simp) regs

end SubexponentialSAT.Subexp.LocalBasisBatchScheduleBounds

end OAI.Algorithms
