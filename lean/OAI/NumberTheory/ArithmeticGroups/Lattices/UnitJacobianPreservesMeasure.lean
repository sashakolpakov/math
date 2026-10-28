import Mathlib.MeasureTheory.Function.Jacobian

/-! # Unit Jacobian Preserves Measure -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.UnitJacobianPreservesMeasure.Construction

noncomputable section

/-! A differentiable homeomorphism with determinant-one derivative
preserves additive Haar measure. -/

open _root_.MeasureTheory _root_.MeasureTheory.Measure

theorem measurePreserving_homeomorph_of_det_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (e : E ≃ₜ E) (μ : Measure E) [IsAddHaarMeasure μ]
    (D : E → E →L[ℝ] E) (hD : ∀ x, HasFDerivAt e (D x) x)
    (hdet : ∀ x, (D x).toLinearMap.det = 1) : MeasurePreserving e μ μ := by
  refine ⟨e.continuous.measurable, ?_⟩
  have h := map_withDensity_abs_det_fderiv_eq_addHaar μ
    (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hD x).hasFDerivWithinAt) e.injective.injOn
  simpa only [Measure.restrict_univ, hdet, abs_one, ENNReal.ofReal_one,
    withDensity_const, one_smul, Set.image_univ, e.surjective.range_eq] using h

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.UnitJacobianPreservesMeasure.Construction
