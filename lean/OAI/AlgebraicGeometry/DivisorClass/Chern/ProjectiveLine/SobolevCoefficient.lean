import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveLine.Gradient
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.ScaledCoefficient

/-! # Sobolev Coefficient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original bundle principal coefficient with the exact 2πi conversion required by the native normalized Sobolev gradient. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineSobolevCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
      GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  Chern.Complex.ScaledCoefficient.complexScaleCoefficient (2 * Real.pi * Complex.I) (h.projectiveLineGradientCoefficient V e n i z)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineSobolevCoefficient_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) (v w : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    inner ℝ (h.projectiveLineSobolevCoefficient V e n i z v) w =
      inner ℝ (h.projectiveLineGradientCoefficient V e n i z ((2 * Real.pi * Complex.I : ℂ) • v))
        ((2 * Real.pi * Complex.I : ℂ) • w) :=
  Chern.Complex.ScaledCoefficient.complexScaleCoefficient_pair _ _ v w

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineSobolevCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveLineSobolevCoefficient V e n i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :=
  Chern.Complex.ScaledCoefficient.complexScaleCoefficient_smoothOn _ _ (h.projectiveLineGradientCoefficient_smooth V e he n i)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineSobolevCoefficient_uniform_lower (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hT : IsCompact T)
    (hs : T ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ T, ∀ v : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (h.projectiveLineSobolevCoefficient V e n i z v) v := by
  have H := h.projectiveLineGradientCoefficient_uniform_lower V e he n i hT hs
  have hk : 0 < ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2 := by
    apply sq_pos_of_pos
    apply norm_pos_iff.mpr
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  refine ⟨H.choose * ‖(2 * Real.pi * Complex.I : ℂ)‖ ^ 2, mul_pos H.choose_spec.1 hk, fun z hz v => ?_⟩
  exact Chern.Complex.ScaledCoefficient.complexScaleCoefficient_lower _ _ H.choose (H.choose_spec.2 z hz) v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
