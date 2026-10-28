import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.ChartField
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.OuterCutoffNeighborhood
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzTestIntegral

/-! # Schwartz Outer Field -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzOuterField

noncomputable section

/-! The constructed outer cutoff gives the exact prescribed compact chart field of the original inserted test. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem holomorphicLineAntiSchwartzFrameInsertion_outer_field (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :
    HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
      (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs)
      (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i g hg hs)
      (AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val =
        fun z => g z • OneCovectorAntiProjection.oneCovectorAntiProjection
          ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c z)) := by
  let t := AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c
  have hout := congrArg (fun a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 => a.val)
    (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_fixes_test V u e he i g hg hs c)
  have hin := SchwartzTestCutoff.holomorphicLineAntiSchwartzFrameInsertion_cutoff V u e he i g hg hs c
  have hfield := HolomorphicCompact.ChartField.holomorphicLineCompactChartField_cutoff_congr V e i 1
    (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
    (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs)
    (OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) t.val t.val (hout.trans hin.symm)
  exact hfield.trans (funext (SchwartzTestIntegral.holomorphicLineAntiSchwartzFrameInsertion_compact_field V e he i g hg hs c))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzOuterField
