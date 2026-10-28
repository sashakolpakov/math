import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.BochnerTransport
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzBochnerIntegral
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LocalizedGreenSchwartz

/-! # Bochner Test -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.BochnerTest

noncomputable section

/-! The actual weak Green solution satisfies the complete native Bochner matrix test equation. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicSmoothGreenSchwartzBochnerTest (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (_ : h.smoothDolbeaultOneCoercive V)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h),
    let f := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs
    let hf := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs
    let hsf := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i g hg hs
    let q := SchwartzMap.smulLeftCLM _ g c
    Holomorphic.BochnerFunctional.holomorphicMetricH1BochnerTestFunctional V h e he i f hf hsf q
      (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_compact g hg c) ((Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_tsupport g c).trans hs)
      (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h v) =
      (inner ℂ v (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h
        (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c))).re

private abbrev greenTransportEquation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (_hc : h.smoothDolbeaultOneCoercive V)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :=
  (Holomorphic.BochnerTransport.holomorphicMetricSmoothEnergy_bochner_transport V h e he i
        (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
        (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs)
        (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i g hg hs)
        (SchwartzMap.smulLeftCLM _ g c) (Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_compact g hg c) ((Analysis.HodgeTheory.Decomposition.ChartCoefficientFaithful.Constructions.schwartz_cutoff_tsupport g c).trans hs)
        (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c)
        (Holomorphic.SchwartzBochnerIntegral.holomorphicLineAntiSchwartzFrameInsertion_outer_schwartz_field V e he i g hg hs c)
        (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h v)
        (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (Holomorphic.LocalizedGreenSchwartz.holomorphicMetricLocalizedSmoothWeakSolution V h e he i g hg hs v))
        (Holomorphic.BochnerTransport.holomorphicMetricLocalizedSmoothWeakSolution_source_apply V h e he i g hg hs v)
        (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_fixes_test V u e he i g hg hs c))

private abbrev greenLaplacianEquation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hc : h.smoothDolbeaultOneCoercive V)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :=
  (congrArg Complex.re (Holomorphic.LocalizedGreenSchwartz.holomorphicMetricLocalizedSmoothWeakSolution_laplacian_test V h e he i g hg hs hc c v))

abbrev holomorphicMetricSmoothGreen_schwartz_bochner_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hc : h.smoothDolbeaultOneCoercive V)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :=
  (greenTransportEquation V h e he i g hg hs hc c v).trans (greenLaplacianEquation V h e he i g hg hs hc c v)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.BochnerTest
