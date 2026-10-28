import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.BochnerTestField
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.SchwartzOuterField
import OAI.AlgebraicGeometry.DivisorClass.Chern.SchwartzCovectorField

/-! # Schwartz Bochner Integral -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The original weak Laplacian integral against each actual inserted Schwartz test equals its complete compact Bochner density. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem Holomorphic.SchwartzBochnerIntegral.holomorphicLineAntiSchwartzFrameInsertion_outer_schwartz_field (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace}
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :
    HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs)
      (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs)
      (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val =
        fun z => OneCovectorAntiProjection.oneCovectorAntiProjection (SchwartzCovectorField.schwartzCovectorField
          (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (SchwartzMap.smulLeftCLM _ g c) z) := by
  apply (Holomorphic.SchwartzOuterField.holomorphicLineAntiSchwartzFrameInsertion_outer_field V e he i g hg hs c).trans
  funext z
  have hq := SchwartzMap.smulLeftCLM_apply_apply g.hasTemperateGrowth c z
  have hp := congrArg (fun v : Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1 =>
    OneCovectorAntiProjection.oneCovectorAntiProjection ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm v)) hq
  have hsm := map_smul (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (g z) (c z)
  exact (hp.trans ((congrArg OneCovectorAntiProjection.oneCovectorAntiProjection hsm).trans (OneCovectorAntiProjection.oneCovectorAntiProjection_complex_smul _ _))).symm

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.schwartzWeakBochner_integral (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    let f := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs
    let hf := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs
    let hsf := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i g hg hs
    let t := Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c
    let p := SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (SchwartzMap.smulLeftCLM _ g c)
    (h.formIntegralPair V 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val (h.smoothDolbeaultLaplacianOne V t)).re =
      ∫ z, h.projectiveBochnerWeakPair V e i (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hsf a.val) p z := by
  let f := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff V u e he i g hg hs
  let hf := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_smooth V u e he i g hg hs
  let hsf := Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_support V u e he i g hg hs
  let t := Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c
  let p := SchwartzCovectorField.schwartzCovectorField (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1 (SchwartzMap.smulLeftCLM _ g c)
  have hB := h.compactWeakBochner_test_field V e he i f hf hsf a t p
    ((SchwartzCovectorField.schwartzCovectorField_smooth _ 1 (SchwartzMap.smulLeftCLM _ g c)).differentiable (by simp))
    (Holomorphic.SchwartzBochnerIntegral.holomorphicLineAntiSchwartzFrameInsertion_outer_schwartz_field V e he i g hg hs c)
  have hfix := congrArg (fun v : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 =>
    (h.formIntegralPair V 1 (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a).val (h.smoothDolbeaultLaplacianOne V v)).re)
    (Holomorphic.OuterCutoffNeighborhood.holomorphicSchwartzOuterFrameCutoff_fixes_test V u e he i g hg hs c)
  exact hfix.symm.trans hB

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
