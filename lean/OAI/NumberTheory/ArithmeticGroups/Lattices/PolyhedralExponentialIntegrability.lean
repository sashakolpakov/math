import OAI.NumberTheory.ArithmeticGroups.Lattices.PolyhedralDecayBound
import OAI.NumberTheory.ArithmeticGroups.Lattices.ExponentialNormIntegrability

/-! # Polyhedral Exponential Integrability -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PolyhedralExponentialIntegrability.Construction

noncomputable section

/-! Exponential densities defined by a separating family of linear
forms have finite mass on truncated polyhedral cones. -/

open _root_.MeasureTheory Set

theorem integrableOn_exp_neg_sum_separating_forms
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (f : ι → Module.Dual ℝ E) (hf : ∀ x, (∀ i, f i x = 0) → x = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn (fun x => Real.exp (-(∑ i, f i x))) {x | ∀ i, -t ≤ f i x} μ := by
  obtain ⟨c, hc, hbound⟩ := PolyhedralDecayBound.Construction.separating_forms_lower_bound f hf
  have hS : IsClosed {x | ∀ i, -t ≤ f i x} := by
    simp only [Set.ofPred_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (f i).continuous_of_finiteDimensional
  have hsum : Continuous (fun x => ∑ i, f i x) :=
    continuous_finsetSum _ (fun i _ => (f i).continuous_of_finiteDimensional)
  have hm := (Real.continuous_exp.comp hsum.neg).aestronglyMeasurable
    (μ := μ.restrict {x | ∀ i, -t ≤ f i x})
  apply ((ExponentialNormIntegrability.Construction.integrable_exp_neg_mul_norm μ c hc).const_mul
    (Real.exp (2 * Fintype.card ι * t))).integrableOn.mono' hm
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  change ‖Real.exp (-(∑ i, f i x))‖ ≤ Real.exp (2 * Fintype.card ι * t) * Real.exp (-c * ‖x‖)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have he := hbound t ht x hx
  linarith

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PolyhedralExponentialIntegrability.Construction
