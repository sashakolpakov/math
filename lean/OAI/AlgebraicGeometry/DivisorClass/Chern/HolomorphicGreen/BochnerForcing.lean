import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.BochnerTest
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.AntiOneSourcePair

/-! # Bochner Forcing -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.BochnerForcing

noncomputable section

/-! Both sides of the actual Green Bochner equation are expressed in the original bounded chart localizations. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicSmoothGreenBochnerFrameEquation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
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
      inner ℝ (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hsf ((h.antiOneL2Submodule V).subtypeL v))
        ((h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume)

abbrev holomorphicMetricSmoothGreen_bochner_frame_equation (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (hc : h.smoothDolbeaultOneCoercive V)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) := by
  have result :=
    Eq.trans (α := ℝ) (BochnerTest.holomorphicMetricSmoothGreen_schwartz_bochner_test V h e he i g hg hs hc c v)
      (Eq.trans (α := ℝ)
        (h.frameL2_weighted_test_pair_of_cutoff V e he i g hg hs c
          (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
          (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs)
          (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i g hg hs)
          (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_one V u e he i g hg hs) ((h.antiOneL2Submodule V).subtypeL v))
        (congrArg Complex.re (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_source_pair V h v
          (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c))).symm).symm
  exact result

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.BochnerForcing
