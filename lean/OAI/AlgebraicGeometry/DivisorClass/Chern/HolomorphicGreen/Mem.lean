import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicFrame.FrameLocalization
import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeakLaplacian

/-! # Mem -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.Mem

noncomputable section

/-! The actual native weak Green solution has genuine local vector H¹ coefficients and retains the original distributional Laplacian equation. -/

open _root_.TopologicalSpace _root_.MeasureTheory TemperedDistribution
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

def holomorphicMetricSmoothGreenH1Localization (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
  (hs : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h →L[ℂ]
    Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V)) :=
  (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i χ hχ hs).comp (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h)

theorem holomorphicMetricSmoothGreenH1Localization_L2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
  (hs : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (f : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :
    ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (holomorphicMetricSmoothGreenH1Localization V h e he i χ hχ hs f) =
      HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 χ hχ hs
        ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h f)) :=
  HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization_L2 V h e he i χ hχ hs (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h f)

theorem holomorphicMetricSmoothGreen_frame_memSobolev (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
  (hs : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (f : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :
    MemSobolev 1 2
      ((HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 χ hχ hs
        ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h f)) :
          Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
            𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :=
  HolomorphicFrame.FrameLocalization.holomorphicMetricFrameL2Localization_memSobolev V h e he i χ hχ hs (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h f)

theorem holomorphicMetricSmoothGreen_H1_laplacian (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
  (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (χ : V.analyticSpace → ℂ) (hχ : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ χ)
  (hs : tsupport χ ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (hc : h.smoothDolbeaultOneCoercive V)
    (f : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h) :
    (∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
      inner ℂ (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h f) (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h (h.smoothAntiLaplacianOne V a)) =
        inner ℂ f (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a)) ∧
    MemSobolev 1 2
      ((HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 χ hχ hs
        ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h f)) :
          Lp (Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1) 2 (volume : Measure (ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V))) :
            𝓢'(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, Analysis.HodgeTheory.Decomposition.SymbolDifferential.Constructions.ExteriorCoordinates (Analysis.HodgeTheory.Decomposition.AdjointCoefficients.Constructions.ProjectiveRealCoordinateIndex V) 1)) :=
  ⟨Holomorphic.WeakLaplacian.holomorphicMetricSmoothGreen_laplacian_test V h hc f, holomorphicMetricSmoothGreen_frame_memSobolev V h e he i χ hχ hs f⟩

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.Mem
