import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.BochnerTest
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoffSource
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyContinuousExt

/-! # Energy Bochner Test -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyBochnerTest

noncomputable section

/-! The complete native Bochner test equation extends to the actual energy core through its proved smooth density. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicSmoothEnergyBochnerTest (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (_ : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z))
    (v : EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h),
    (inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf v))
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c)))).re =
      BochnerFunctional.holomorphicMetricH1BochnerTestFunctional V h e he i f hf hsf q hq hsq v

private abbrev energyBochnerContinuity (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (_hq : HasCompactSupport q)
    (_hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (_hct : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z)) :=
  Complex.continuous_re.comp
    (((EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h).continuous.comp
      (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf).continuous).inner (𝕜 := ℂ)
        (continuous_const (y := AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h
          (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c)))))

private abbrev energyBochnerFunctionalContinuity (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (_hct : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z)) :=
  BochnerFunctional.holomorphicMetricH1BochnerTestFunctional_continuous V h e he i f hf hsf q hq hsq

private abbrev energyBochnerSmoothEquation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (hct : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z)) :=
  fun a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 => Eq.trans (α := ℝ)
    (EnergyCutoffSource.holomorphicMetricSmoothEnergyCutoff_re_pair_on_smooth V h e he i f hf hsf a
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h
        (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c))))
    (HolomorphicSmooth.BochnerTest.holomorphicMetricSmooth_bochner_test V h e he i f hf hsf q hq hsq c hct a)

abbrev holomorphicMetricSmoothEnergy_bochner_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (q : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (hq : HasCompactSupport q)
    (hsq : tsupport q ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1)
    (hct : HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf c.val = fun z => OneCovectorAntiProjection.oneCovectorAntiProjection
      (SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 q z))
    (v : EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h) := by
  let F := fun w : EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h =>
    (inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf w))
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h
        (h.smoothAntiLaplacianOne V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c)))).re
  let G := BochnerFunctional.holomorphicMetricH1BochnerTestFunctional V h e he i f hf hsf q hq hsq
  exact EnergyContinuousExt.holomorphicMetricSmoothEnergy_continuous_ext V h (G := ℝ) F G
    (energyBochnerContinuity V h e he i f hf hsf q hq hsq c hct)
    (energyBochnerFunctionalContinuity V h e he i f hf hsf q hq hsq c hct)
    (energyBochnerSmoothEquation V h e he i f hf hsf q hq hsq c hct) v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyBochnerTest
