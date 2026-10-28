import OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientConvergence
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! # Coefficient Derivative -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction

noncomputable section

/-! The actual directional derivative of a smooth coefficient field and
strong convergence of its difference coefficients on L2 functions. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def coefficientDerivative (A : E → F →L[ℝ] F) (m : E) : E → F →L[ℝ] F :=
  fun x => fderiv ℝ A x m

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem differenceCoefficient_tendsto (A : E → F →L[ℝ] F)
    (hA : Differentiable ℝ A) (m x : E) :
    Tendsto (fun t : ℝ => DifferenceProduct.CM.Construction.differenceCoefficient A m t x) (𝓝[≠] 0)
      (𝓝 (coefficientDerivative A m x)) :=
  ((hA x).hasFDerivAt.hasLineDerivAt m).tendsto_slope_zero

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem coefficientDerivative_bound (A : E → F →L[ℝ] F)
    (hA : Differentiable ℝ A) {L : NNReal} (hL : LipschitzWith L A) (m x : E) :
    ‖coefficientDerivative A m x‖ ≤ (L : ℝ) * ‖m‖ :=
  le_of_tendsto (differenceCoefficient_tendsto A hA m x).norm
    (Filter.Eventually.of_forall (fun t => DifferenceProduct.CM.Construction.differenceCoefficient_lipschitz_bound A hL m x t))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem coefficientDerivative_continuous (A : E → F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) (m : E) : Continuous (coefficientDerivative A m) :=
  (hA.continuous_fderiv (by simp)).clm_apply continuous_const

theorem differenceCoefficientLp_tendsto (A : E → F →L[ℝ] F)
    (hA : ContDiff ℝ ∞ A) {L : NNReal} (hL : LipschitzWith L A)
    {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (m : E) (u : Lp F 2 (volume : Measure E)) :
    Tendsto (fun t : ℝ => LpCoefficients.CM.Construction.boundedFieldLp (DifferenceProduct.CM.Construction.differenceCoefficient A m t)
      (DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hA.continuous.aestronglyMeasurable m t)
      (DifferenceProduct.CM.Construction.differenceCoefficient_bound A (Filter.Eventually.of_forall hC) m t) u) (𝓝[≠] 0)
      (𝓝 (LpCoefficients.CM.Construction.boundedFieldLp (coefficientDerivative A m)
        (coefficientDerivative_continuous A hA m).aestronglyMeasurable
        (Filter.Eventually.of_forall (coefficientDerivative_bound A (hA.differentiable (by simp)) hL m)) u)) := by
  let hAm := hA.continuous.aestronglyMeasurable (μ := (volume : Measure E))
  have hD (t : ℝ) : ∀ᵐ x ∂(volume : Measure E),
      ‖DifferenceProduct.CM.Construction.differenceCoefficient A m t x‖ ≤ (L : ℝ) * ‖m‖ :=
    Filter.Eventually.of_forall (fun x => DifferenceProduct.CM.Construction.differenceCoefficient_lipschitz_bound A hL m x t)
  have h := CoefficientConvergence.CM.Construction.boundedFieldLp_tendsto (fun t => DifferenceProduct.CM.Construction.differenceCoefficient A m t) (coefficientDerivative A m)
    (fun t => DifferenceProduct.CM.Construction.differenceCoefficient_measurable A hAm m t)
    (coefficientDerivative_continuous A hA m).aestronglyMeasurable hD
    (Filter.Eventually.of_forall (coefficientDerivative_bound A (hA.differentiable (by simp)) hL m))
    (Filter.Eventually.of_forall (fun x => differenceCoefficient_tendsto A
      (hA.differentiable (by simp)) m x)) u
  exact h

theorem translatedCoefficientLp_tendsto_varying (A : E → F →L[ℝ] F)
    (hA : Continuous A) {C : ℝ} (hC : ∀ x, ‖A x‖ ≤ C) (m : E)
    (u : ℝ → Lp F 2 (volume : Measure E)) (u₀ : Lp F 2 (volume : Measure E))
    (hu : Tendsto u (𝓝[≠] 0) (𝓝 u₀)) :
    Tendsto (fun t : ℝ => LpCoefficients.CM.Construction.boundedFieldLp (DifferenceProduct.CM.Construction.translatedCoefficient A (t • m))
      (DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hA.aestronglyMeasurable (t • m))
      (DifferenceProduct.CM.Construction.translatedCoefficient_bound A (Filter.Eventually.of_forall hC) (t • m)) (u t)) (𝓝[≠] 0)
      (𝓝 (LpCoefficients.CM.Construction.boundedFieldLp A hA.aestronglyMeasurable (Filter.Eventually.of_forall hC) u₀)) := by
  apply CoefficientConvergence.CM.Construction.boundedFieldLp_tendsto_varying (fun t => DifferenceProduct.CM.Construction.translatedCoefficient A (t • m)) A
    (fun t => DifferenceProduct.CM.Construction.translatedCoefficient_measurable A hA.aestronglyMeasurable (t • m))
    hA.aestronglyMeasurable
    (fun t => DifferenceProduct.CM.Construction.translatedCoefficient_bound A (Filter.Eventually.of_forall hC) (t • m))
    (Filter.Eventually.of_forall hC) _ u u₀ hu
  apply Filter.Eventually.of_forall
  intro x
  have ht : Continuous (fun t : ℝ => A (x + t • m)) :=
    hA.comp (continuous_const.add (continuous_id.smul continuous_const))
  simpa only [DifferenceProduct.CM.Construction.translatedCoefficient, zero_smul, add_zero] using
    ((ht.tendsto 0).mono_left nhdsWithin_le_nhds)

end

end OAI.AlgebraicGeometry.ComplexMultiplication.HodgeComparison.CoefficientDerivative.CM.Construction
