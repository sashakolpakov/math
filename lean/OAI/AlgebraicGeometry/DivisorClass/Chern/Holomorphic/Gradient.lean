import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.FrameLocalization
import OAI.AlgebraicGeometry.DivisorClass.Chern.VectorGradientNormalization
import OAI.AlgebraicGeometry.DivisorClass.Chern.GradientTensorReconstruction

/-! # Gradient -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Gradient

noncomputable section

/-! The actual H¹ localization gradient reconstructs the literal ordinary derivative of the original compact bundle chart field. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

private theorem holomorphicMetricFrameH1_gradient_on_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ∀ᵐ z ∂(volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      (2 * Real.pi * Complex.I : ℂ) •
        Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
          (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hs (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a)) z =
        WithLp.toLp 2 (fun j => fderiv ℝ (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i 1 f hf hs a.val) z
          (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) j)) := by
  exact VectorGradientNormalization.vectorGradient_physical_of_coordinate_eq (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
    (HolomorphicFrame.Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i 1 f hf hs a.val) _
    (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization_on_smooth V h e he i f hf hs a)

def HolomorphicFrameH1GradientTensorOnSmooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
    ∀ᵐ z ∂(volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)),
      GradientTensorCoordinates.covectorGradientTensor (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
        ((2 * Real.pi * Complex.I : ℂ) •
          Analysis.HodgeTheory.Decomposition.VectorGradient.Constructions.vectorSobolevGradient (F := Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))
            (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hs (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a)) z) =
        fderiv ℝ (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) z

theorem holomorphicMetricFrameH1_gradient_tensor_on_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicFrameH1GradientTensorOnSmooth V h := by
  intro e he i f hf hs a
  exact (holomorphicMetricFrameH1_gradient_on_smooth V h e he i f hf hs a).mono (fun z hz =>
    GradientTensorReconstruction.covectorGradientTensor_eq_of_coefficients (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 _
      (fderiv ℝ (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) z) (fun j =>
        (congrArg (fun v : GradientTensorCoordinates.CovectorGradientCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 => v j) hz).trans
          (CoefficientDerivative.holomorphicLineFrameCoefficient_derivative V e he i 1 f hf hs a.val z _)))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.Gradient
