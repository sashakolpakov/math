import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.TestCutoffIndependence
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.TestRepresentation

/-! # Outer Test Representation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! The native global test pairing is represented with any actual outer chart cutoff equal to one on the test support. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.frameL2_weighted_test_pair_of_cutoff (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
    (hsχ : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (hχone : ∀ z ∈ tsupport g, χ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 1)
    (v : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1) :
    inner ℝ (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 χ hχ hsχ v)
      ((h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume) =
      (inner ℂ v (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1
        (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c).val)).re := by
  let q := h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c
  have hq := h.projectiveWeightedAntiSchwartzTest_tsupport V e he i g hg hs c
  have hsame : ∀ z ∈ tsupport q, χ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) =
      Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) := by
    intro z hz
    exact (hχone z (hq hz)).trans (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_one V u e he i g hg hs z (hq hz)).symm
  have hp := HolomorphicFrame.TestCutoffIndependence.holomorphicMetricFrameL2Localization_pair_cutoffs V e he i 1 χ hχ hsχ
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) q (hq.trans hs) hsame h v
  exact hp.trans (h.frameL2_weighted_test_pair V e he i g hg hs c v)

--
theorem Holomorphic.OuterTestRepresentation.holomorphicMetricSmoothGreenH1_weighted_test_pair_of_cutoff (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
    (hsχ : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (hχone : ∀ z ∈ tsupport g, χ (Analysis.HodgeTheory.Decomposition.MeasureVolume.Constructions.chartCoordinateInverse V e z) = 1)
    (v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :
    inner ℝ (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
      (HolomorphicGreen.Mem.holomorphicMetricSmoothGreenH1Localization V h e he i χ hχ hsχ v))
      ((h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume) =
      (inner ℂ (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h v) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h
        (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c))).re := by
  let q := (h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume
  have hloc := HolomorphicGreen.Mem.holomorphicMetricSmoothGreenH1Localization_L2 V h e he i χ hχ hsχ v
  have hp := h.frameL2_weighted_test_pair_of_cutoff V e he i g hg hs c χ hχ hsχ hχone
    ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h v))
  have hi := congrArg (fun a : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 =>
    (inner ℂ ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h v)) a).re)
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val V h (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c))
  exact (congrArg (fun a => inner ℝ a q) hloc).trans (hp.trans hi.symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
