import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Gradient
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.SchwartzTests
import OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCovectorGradient
import OAI.AlgebraicGeometry.DivisorClass.Chern.ProjectiveBochner.PairSupport

/-! # Bochner Test Density -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerTestDensity

noncomputable section

/-! The complete native compact Bochner density equals the two actual adjoint-test pairings of the original H¹ localization. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicFrameH1BochnerTestDensity (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
    let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf a.val
    let p := SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q
    let D := Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
      (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hsf (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a))
    ∀ᵐ z ∂(volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      h.projectiveBochnerWeakPair V e i s p z =
        inner ℝ (D z) (h.projectiveBochnerGradientSchwartzTest V e he i q hq hsq z) +
        inner ℝ (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i 1 f hf hsf a.val z)
          (h.projectiveBochnerValueSchwartzTest V e he i q hq hsq z)

theorem holomorphicMetricFrameH1_bochner_test_density (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicFrameH1BochnerTestDensity V h := by
  intro e he i f hf hsf q hq hsq a
  let b := stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)
  let s := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf a.val
  let p := SchwartzCovectorField.schwartzCovectorField b.toBasis 1 q
  let D := Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) b
    (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hsf (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a))
  let c := HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i 1 f hf hsf a.val
  let dq := Compact.SchwartzGradient.compactSchwartzGradient b q hq
  apply (Gradient.holomorphicMetricFrameH1_gradient_tensor_on_smooth V h e he i f hf hsf a).mono
  intro z hgrad
  by_cases hz : z ∈ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)
  · have hcoords := (TensorGradientCoordinates.covectorGradientTensor_right_inverse b.toBasis 1 _).symm.trans
      (congrArg (TensorGradientCoordinates.covectorTensorGradientCoordinates b.toBasis 1) hgrad)
    have hm := h.projectiveBochnerWeakPair_matrix V e i s p hz (D z) (dq z) hcoords
      (SchwartzCovectorGradient.compactSchwartzGradient_covector b 1 q hq z)
    have hvalues := congrArg₂ (fun av cv : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 =>
      inner ℝ (h.projectiveLineSobolevCoefficient V e 1 i z (D z)) (dq z) +
      inner ℝ (h.projectiveLineValueGradientCoefficient V e 1 i z av) (dq z) +
      inner ℝ (h.projectiveLineGradientValueCoefficient V e 1 i z (D z)) cv +
      inner ℝ (h.projectiveLineWeakValueCoefficient V e i z av) cv)
      (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_coefficients V e i 1 f hf hsf a.val z)
      (SchwartzCovectorField.schwartzCovectorField_coordinates b.toBasis 1 q z)
    exact hm.trans (hvalues.trans (h.projectiveBochnerSchwartzTests_pair V e he i q hq hsq z (c z) (D z)))
  · have hsource : z ∉ tsupport s := fun ht => hz (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_tsupport V e i 1 f hf hsf a.val ht)
    have htest : z ∉ tsupport q := fun ht => hz (hsq ht)
    have hqzero : q z = 0 := image_eq_zero_of_notMem_tsupport htest
    have hdqzero : dq z = 0 := image_eq_zero_of_notMem_tsupport
      (fun ht => htest (Compact.SchwartzGradient.compactSchwartzGradient_tsupport b q hq ht))
    have hp := h.projectiveBochnerSchwartzTests_pair V e he i q hq hsq z (c z) (D z)
    have hmzero : inner ℝ (h.projectiveLineSobolevCoefficient V e 1 i z (D z)) (dq z) +
        inner ℝ (h.projectiveLineValueGradientCoefficient V e 1 i z (c z)) (dq z) +
        inner ℝ (h.projectiveLineGradientValueCoefficient V e 1 i z (D z)) (q z) +
        inner ℝ (h.projectiveLineWeakValueCoefficient V e i z (c z)) (q z) = 0 := by
      rw [hqzero, hdqzero, inner_zero_right, inner_zero_right, inner_zero_right, inner_zero_right]
      norm_num
    exact (h.projectiveBochnerWeakPair_zero_left V e i s p z hsource).trans (hp.symm.trans hmzero).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerTestDensity
