import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Bound
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.Localization
import OAI.AlgebraicGeometry.DivisorClass.Chern.VectorSobolevMembership

/-! # Frame Localization -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.FrameLocalization

noncomputable section

/-! Actual H¹ localization of the completed original smooth bundle energy space, with its unchanged L² realization. -/

open _root_.TopologicalSpace _root_.MeasureTheory TemperedDistribution
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

def holomorphicMetricFrameH1Localization (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) : Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h →L[ℂ]
    Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (Bound.holomorphicLineFrameH1Smooth V e he i f hf hs).extendOfNorm (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h)

def HolomorphicFrameH1LocalizationOnSmooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
    holomorphicMetricFrameH1Localization V h e he i f hf hs (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a) =
      Bound.holomorphicLineFrameH1Smooth V e he i f hf hs a

theorem holomorphicMetricFrameH1Localization_on_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicFrameH1LocalizationOnSmooth V h := by
  intro e he i f hf hs a
  have H := Bound.holomorphicLineFrameH1Smooth_bound V h e he i f hf hs
  exact LinearMap.extendOfNorm_eq (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion_dense V h)
    ⟨H.choose, H.choose_spec.2⟩ a

def HolomorphicFrameH1LocalizationL2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (v : Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h),
    ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (holomorphicMetricFrameH1Localization V h e he i f hf hs v) =
      Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hs
        ((h.antiOneL2Submodule V).subtypeL (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v))

theorem holomorphicMetricFrameH1Localization_L2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicFrameH1LocalizationL2 V h := by
  intro e he i f hf hs v
  have hc : IsClosed {w : Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h |
      ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (holomorphicMetricFrameH1Localization V h e he i f hf hs w) =
        Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hs
          ((h.antiOneL2Submodule V).subtypeL (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h w))} :=
    isClosed_eq
      ((ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1)).continuous.comp
        (holomorphicMetricFrameH1Localization V h e he i f hf hs).continuous)
      ((Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hs).continuous.comp
        ((h.antiOneL2Submodule V).subtypeL.continuous.comp (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h).continuous))
  refine (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion_dense V h).induction_on v hc (fun a => ?_)
  have hl := congrArg (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1))
    (holomorphicMetricFrameH1Localization_on_smooth V h e he i f hf hs a)
  have hsmooth := (Analysis.HodgeTheory.Decomposition.VectorEmbeddingRange.Constructions.vectorSobolevL2Embedding_schwartz (by norm_num : (0 : ℝ) ≤ 1)
    (Schwartz.holomorphicLineFrameCoefficientsSchwartz V e he i 1 f hf hs a.val)).trans
      (Schwartz.holomorphicLineFrameCoefficientsSchwartz_toLp V e he i 1 f hf hs a.val)
  have hsource : (h.antiOneL2Submodule V).subtypeL
      (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a)) =
        Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 1 a.val := by
    exact (congrArg (fun w : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h => w.val)
      (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion_source V h a)).trans (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val V h a)
  have hr := (congrArg (Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hs) hsource).trans
    (Localization.holomorphicMetricFrameL2Localization_on_smooth V h e he i 1 f hf hs a.val)
  exact (hl.trans hsmooth).trans hr.symm

def HolomorphicFrameL2LocalizationSobolev (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (v : Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h),
    MemSobolev 1 2
      ((Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hs
        ((h.antiOneL2Submodule V).subtypeL (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v)) :
          Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
            𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1))

theorem holomorphicMetricFrameL2Localization_memSobolev (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicFrameL2LocalizationSobolev V h := by
  intro e he i f hf hs v
  exact Eq.mp (congrArg (fun w : Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2
      (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) =>
        MemSobolev 1 2 (w : 𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)))
    (holomorphicMetricFrameH1Localization_L2 V h e he i f hf hs v))
      (VectorSobolevMembership.vectorSobolevEmbedding_memSobolev (holomorphicMetricFrameH1Localization V h e he i f hf hs v))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.FrameLocalization
