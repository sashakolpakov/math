import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorSmooth
import OAI.AlgebraicGeometry.DivisorClass.Chern.Line.EnergyExpansion
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.CrossEnergy

/-! # Gradient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The principal coefficient of half the native full rough Laplacian uses the actual projective density, line weight, and inverse covector metric. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineGradientCoefficient (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    (z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n →L[ℝ]
      GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n :=
  GradientTensorCoefficient.covectorGradientCoefficient (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) ((1 / 2 : ℝ) * ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity V e z * (h.projectiveWeightChart V e i z).re)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineGradientCoefficient_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (n : ℕ) (i : V.analyticSpace)
    {z : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V}
    (hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v w : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n) :
    let b := (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis
    inner ℝ (h.projectiveLineGradientCoefficient V e n i z v) w =
      (1 / 2 : ℝ) * (Line.EnergyExpansion.lineOrdinaryTensorPair b n (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e z) (h.projectiveWeightChart V e i z)
        (GradientTensorCoordinates.covectorGradientTensor b n v) (GradientTensorCoordinates.covectorGradientTensor b n w)).re := by
  rw [HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineGradientCoefficient, GradientTensorCoefficient.covectorGradientCoefficient_pair]
  unfold Line.EnergyExpansion.lineOrdinaryTensorPair
  rw [h.projectiveWeightChart_apply V e i hz]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  simp only [ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity, mul_assoc]

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineGradientCoefficient_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) :
    ContDiffOn ℝ ∞ (h.projectiveLineGradientCoefficient V e n i)
      (ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  exact GradientTensorSmooth.covectorGradientCoefficient_smoothOn _ n _ _ D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    ((contDiffOn_const.mul ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).mono (fun _ hx => hx.1))).mul
      (Complex.reCLM.contDiff.comp_contDiffOn (h.projectiveWeightChart_smooth V e he i)))
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hx.1)
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.projectiveLineGradientCoefficient_uniform_lower (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (n : ℕ) (i : V.analyticSpace) {T : Set (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)} (hT : IsCompact T)
    (hs : T ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    ∃ c : ℝ, 0 < c ∧ ∀ z ∈ T, ∀ v : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) n,
      c * ‖v‖ ^ 2 ≤ inner ℝ (h.projectiveLineGradientCoefficient V e n i z v) v := by
  let D := ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  exact GradientTensorSmooth.covectorGradientCoefficient_uniform_lower _ n _ _ D.isOpen
    ((ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_smooth V e he).mono (fun _ hx => hx.1))
    ((contDiffOn_const.mul ((ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_smooth V e he).mono (fun _ hx => hx.1))).mul
      (Complex.reCLM.contDiff.comp_contDiffOn (h.projectiveWeightChart_smooth V e he i)))
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_symmetric V e he hx.1)
    (fun _ hx => ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric_positive V e he hx.1)
    (by
      intro z hz
      rw [h.projectiveWeightChart_apply V e i hz, Complex.ofReal_re]
      exact mul_pos (mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
        (ComplexMultiplication.HodgeComparison.Metric.CM.Construction.varietyMetricDensity_pos V e he hz.1)) (h.positive i _)) hT hs

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
