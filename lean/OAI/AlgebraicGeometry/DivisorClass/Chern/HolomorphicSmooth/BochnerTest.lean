import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.BochnerTestField
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LaplacianHilbertPair

/-! # Bochner Test -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.BochnerTest

noncomputable section

/-! The original smooth Hilbert Laplacian pairing is the full H¹ Bochner functional for an explicit original cutoff and matching compact test field. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicSmoothBochnerTest (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (_ : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
    (inner ℂ (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a))
      (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c)))).re =
      Holomorphic.BochnerFunctional.holomorphicMetricH1BochnerTestFunctional V h e he i f hf hsf q hq hsq
        (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a)

private abbrev smoothBochnerIntegral (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (_hq : HasCompactSupport q)
    (_hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (_hct : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :=
  congrArg Complex.re (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_inner V h
    (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a) (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c)))

private abbrev smoothBochnerNative (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (_hq : HasCompactSupport q)
    (_hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (hct : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :=
  h.compactWeakBochner_test_field V e he i f hf hsf a c
    (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q)
    ((SchwartzCovectorField.schwartzCovectorField_smooth _ 1 q).differentiable (by simp)) hct

private abbrev smoothBochnerFunctional (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (_hct : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :=
  Holomorphic.BochnerIntegral.holomorphicMetricH1BochnerTestFunctional_on_smooth V h e he i f hf hsf q hq hsq a

abbrev holomorphicMetricSmooth_bochner_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (hct : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :=
  (smoothBochnerIntegral V h e he i f hf hsf q hq hsq c hct a).trans
    ((smoothBochnerNative V h e he i f hf hsf q hq hsq c hct a).trans (smoothBochnerFunctional V h e he i f hf hsf q hq hsq c hct a).symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.BochnerTest
