import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.ChartField
import OAI.AlgebraicGeometry.DivisorClass.Chern.LinearNormIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Projective.DerivativeIntegralBound

/-! # Coefficient Derivative -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CoefficientDerivative

noncomputable section

/-! Literal exterior coordinates preserve the original compact chart derivative and its integral estimates. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (n : ℕ)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))

include he

theorem holomorphicLineFrameCoefficient_derivative (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (z v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    fderiv ℝ (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a) z v =
      Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n
        (fderiv ℝ (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a) z v) := by
  let L := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).toContinuousLinearMap.restrictScalars ℝ
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a
  have heq : HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a = fun y => L (c y) :=
    funext (fun y => (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_coefficients V e i n f hf hs a y).symm)
  have hd := (L.hasFDerivAt.comp z ((HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i n f hf hs a).differentiable (by simp) z).hasFDerivAt).fderiv
  exact (congrArg (fun g => fderiv ℝ g z v) heq).trans (congrArg (fun T => T v) hd)

theorem holomorphicLineFrameCoefficient_norm_integral_le (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n) :
    (∫ z, ‖HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a z‖ ^ 2) ≤
      ‖(Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).toContinuousLinearMap.restrictScalars ℝ‖ ^ 2 *
        Projective.DerivativeIntegralBound.projectiveFieldNormIntegral V n (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a) := by
  let L := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).toContinuousLinearMap.restrictScalars ℝ
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a
  calc
    _ = ∫ z, ‖L (c z)‖ ^ 2 := integral_congr_ae (Filter.Eventually.of_forall (fun z =>
      congrArg (fun w => ‖w‖ ^ 2) (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_coefficients V e i n f hf hs a z).symm))
    _ ≤ _ := LinearNormIntegral.continuousLinearMap_norm_sq_integral_bound volume L c
      (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i n f hf hs a).continuous
      (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i n f hf hs a)

theorem holomorphicLineFrameCoefficient_derivative_integral_le (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ n)
    (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V) :
    (∫ z, ‖fderiv ℝ (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientLinear V e i n f hf hs a) z v‖ ^ 2) ≤
      ‖(Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).toContinuousLinearMap.restrictScalars ℝ‖ ^ 2 *
        Projective.DerivativeIntegralBound.projectiveFieldDirectionalIntegral V n (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a) v := by
  let L := (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis n).toContinuousLinearMap.restrictScalars ℝ
  let c := HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i n f hf hs a
  have hc : Continuous (fun z => fderiv ℝ c z v) :=
    ((HolomorphicCompact.ChartField.holomorphicLineCompactChartField_smooth V e he i n f hf hs a).continuous_fderiv (by simp)).clm_apply continuous_const
  have hcompact : HasCompactSupport (fun z => fderiv ℝ c z v) :=
    (HolomorphicCompact.ChartField.holomorphicLineCompactChartField_compact V e i n f hf hs a).fderiv_apply ℝ v
  calc
    _ = ∫ z, ‖L (fderiv ℝ c z v)‖ ^ 2 := integral_congr_ae (Filter.Eventually.of_forall (fun z =>
      congrArg (fun w => ‖w‖ ^ 2) (holomorphicLineFrameCoefficient_derivative V e he i n f hf hs a z v)))
    _ ≤ _ := LinearNormIntegral.continuousLinearMap_norm_sq_integral_bound volume L _ hc hcompact

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CoefficientDerivative
