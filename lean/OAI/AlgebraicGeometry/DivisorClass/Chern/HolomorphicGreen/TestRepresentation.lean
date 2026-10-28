import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.TestRepresentation
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.Mem

/-! # Test Representation -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.TestRepresentation

noncomputable section

/-! The actual H¹ chart localization of the native weak Green solution represents the original global antiholomorphic test pairing. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

--
theorem holomorphicMetricSmoothGreenH1_weighted_test_pair (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (hg : HasCompactSupport g)
    (hs : tsupport g ⊆ ConnectionChartDerivative.projectiveOpenChartDomain V e (Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i))
    (c : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))
    (v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :
    inner ℝ (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)
      (Mem.holomorphicMetricSmoothGreenH1Localization V h e he i (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs)
        (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
        (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) v))
      ((h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume) =
      (inner ℂ (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h v) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h
        (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c))).re := by
  let f := Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff V u e he i g hg hs
  let q := (h.projectiveWeightedAntiSchwartzTest V e he i g hg hs c).toLp 2 volume
  have hloc := Mem.holomorphicMetricSmoothGreenH1Localization_L2 V h e he i f
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_smooth V u e he i g hg hs)
    (Holomorphic.AntiSchwartzTests.holomorphicSchwartzFrameCutoff_support V u e he i g hg hs) v
  have hp := h.frameL2_weighted_test_pair V e he i g hg hs c
    ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h v))
  have hi := congrArg (fun a : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 =>
    (inner ℂ ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h v)) a).re)
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val V h (Holomorphic.AntiSchwartzTests.holomorphicLineAntiSchwartzFrameInsertion V u e he i g hg hs c))
  exact (congrArg (fun a => inner ℝ a q) hloc).trans (hp.trans hi.symm)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.TestRepresentation
