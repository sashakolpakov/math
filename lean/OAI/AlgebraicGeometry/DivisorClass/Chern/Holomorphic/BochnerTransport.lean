import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyBochnerTest
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LocalizedGreenSchwartz

/-! # Bochner Transport -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerTransport

noncomputable section

/-! Exact transport of the full native Bochner test equation across fixed test cutoffs and the constructed localized Green source. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicSmoothEnergyBochnerTransport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
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
    (v : EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h)
    (z : AntiOneSourcePair.HolomorphicAntiOneL2With V h)
    (_ : z = EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf v))
    (_ : HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf c = c),
    BochnerFunctional.holomorphicMetricH1BochnerTestFunctional V h e he i f hf hsf q hq hsq v =
      (inner ℂ z (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V c))).re

theorem holomorphicMetricSmoothEnergy_bochner_transport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicSmoothEnergyBochnerTransport V h := by
  intro e he i f hf hsf q hq hsq c hct v z hsource hfix
  exact Eq.trans (α := ℝ) (EnergyBochnerTest.holomorphicMetricSmoothEnergy_bochner_test V h e he i f hf hsf q hq hsq c hct v).symm
    (Eq.trans (α := ℝ)
      (congrArg (fun t : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 =>
        (inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h f hf v))
          (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V t))).re) hfix)
      (congrArg (fun x : AntiOneSourcePair.HolomorphicAntiOneL2With V h =>
        (inner ℂ x (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V c))).re) hsource).symm)

def HolomorphicLocalizedSmoothWeakSolutionSource (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (v : AntiOneSourcePair.HolomorphicAntiOneL2With V h),
    EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (LocalizedGreenSchwartz.holomorphicMetricLocalizedSmoothWeakSolution V h e he i g hg hs v) =
      EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h
        (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
          (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs) (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h v))

theorem holomorphicMetricLocalizedSmoothWeakSolution_source_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicLocalizedSmoothWeakSolutionSource V h := by
  intro e he i g hg hs v
  exact rfl

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerTransport
