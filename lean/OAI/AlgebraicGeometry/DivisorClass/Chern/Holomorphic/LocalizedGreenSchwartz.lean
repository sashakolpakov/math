import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoffLaplacian
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OuterCutoffNeighborhood
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OuterTestRepresentation

/-! # Localized Green Schwartz -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LocalizedGreenSchwartz

noncomputable section

/-! The actual native Green solution localized by a constructed outer cutoff retains the original weak Laplacian equation for every prescribed compact chart test. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

def holomorphicMetricLocalizedSmoothWeakSolution (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i)) :
    AntiOneSourcePair.HolomorphicAntiOneL2With V h →L[ℂ] EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h :=
  (EnergyCutoff.holomorphicMetricSmoothEnergyCutoff V h (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
    (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs)).comp
      (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h)

def HolomorphicLocalizedSmoothWeakSolutionLaplacianTest (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (_ : h.smoothDolbeaultOneCoercive V)
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (v : AntiOneSourcePair.HolomorphicAntiOneL2With V h),
    inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (holomorphicMetricLocalizedSmoothWeakSolution V h e he i g hg hs v))
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V
        (AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c))) =
      inner ℂ v (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c))

theorem holomorphicMetricLocalizedSmoothWeakSolution_laplacian_test (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicLocalizedSmoothWeakSolutionLaplacianTest V h := by
  intro e he i g hg hs hc c v
  let t := AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c
  have hp := EnergyCutoffLaplacian.holomorphicMetricSmoothGreenCutoff_laplacian_test V h e he i
    (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
    (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs)
    (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_near V u e he i g hg hs) hc t v
  have ht := SchwartzTestCutoff.holomorphicLineAntiSchwartzFrameInsertion_cutoff_anti V u e he i g hg hs c
  exact Eq.mp (congrArg (fun a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 =>
    inner ℂ (EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (holomorphicMetricLocalizedSmoothWeakSolution V h e he i g hg hs v))
      (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V a)) =
        inner ℂ v (AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)) ht) hp

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LocalizedGreenSchwartz
