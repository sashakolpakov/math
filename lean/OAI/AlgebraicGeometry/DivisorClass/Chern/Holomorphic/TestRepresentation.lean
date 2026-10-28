import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TestSourceCoordinates
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Localization

/-! # Test Representation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

section

/-! The original global pairing with an inserted test depends continuously on the actual bounded frame localization. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
  (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
  (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameCoefficientsLp_weighted_test_pair
    (a : HolomorphicLine.AntiForms.HolomorphicLineSmoothForm u ⊤ 1) :
    inner ℝ (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i 1 (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) a)
      ((h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume) =
      (h.formIntegralPair V 1 a (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val).re := by
  let f := Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs
  let q := h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c
  let P := Line.TensorMetricTest.lineMetricTestPair (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1
    (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanMetric V e) (h.projectiveWeightChart V e i) (Analysis.HodgeTheory.Decomposition.EuclideanForms.Constructions.euclideanChartForm V e 1 (a.val i).extension)
    (fun x => g x • OneCovectorAntiProjection.oneCovectorAntiProjection
      ((Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.exteriorCoordinateEquiv (stdOrthonormalBasis ℝ (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)).toBasis 1).symm (c x)))
  have hsource := (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficients_memLp V e he i 1 f
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) a).coeFn_toLp
  have htest := SchwartzMap.coeFn_toLp q (p := 2) (μ := volume)
  have hi : inner ℝ (HolomorphicFrame.CoordinatesLp.holomorphicLineFrameCoefficientsLp V e he i 1 f
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) a) (q.toLp 2 volume) =
        ∫ z, (P z).re := by
    rw [L2.inner_def]
    apply integral_congr_ae
    apply Filter.Eventually.mono (hsource.and htest)
    intro z hz
    exact (congrArg₂ (fun v w => inner ℝ v w) hz.1 hz.2).trans
      (h.frameCoefficient_weighted_test_pair V e he i g hg hs a c z)
  exact hi.trans ((integral_re (h.schwartzFramePair_integrable V e he i g hg hs c a)).trans
    (congrArg Complex.re (h.schwartzFramePair_integral V e he i g hg hs c a)))

end

/-! The original global bundle test pairing is represented by the actual bounded Euclidean frame localization for every element of the original Hilbert completion. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameL2_weighted_test_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (v : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1) :
    inner ℝ (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) v)
      ((h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume) =
      (inner ℂ v (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1
        (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val)).re := by
  let f := Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs
  let L := HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 f
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs)
  let q := (h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume
  let t := Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1
    (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val
  have hleft : Continuous (fun x : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 => inner ℝ (L x) q) :=
    L.continuous.inner continuous_const
  have hright : Continuous (fun x : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 => (inner ℂ x t).re) :=
    Complex.continuous_re.comp (continuous_id.inner continuous_const)
  have heq := (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_dense V h 1).equalizer hleft hright (by
    funext a
    have hl := HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization_on_smooth V h e he i 1 f
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
      (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) a
    have hp := h.frameCoefficientsLp_weighted_test_pair V e he i g hg hs c a
    have hi := Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_inner V h 1 a
      (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val
    exact (congrArg (fun z => inner ℝ z q) hl).trans (hp.trans (congrArg Complex.re hi).symm))
  exact congrFun heq v

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
