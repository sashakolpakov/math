import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.Mem
import OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffDifferential

/-! # Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.Cutoff

noncomputable section

/-! Sobolev cutoff of the actual Green coordinates is exactly scalar multiplication of the original bounded L² chart localization. -/

open _root_.TopologicalSpace _root_.MeasureTheory
open scoped _root_.Manifold ContDiff SchwartzMap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open OAI.Analysis.HodgeTheory.Decomposition.VectorCutoffDifferential.Constructions

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicSmoothGreenCutoffL2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hsf : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) (g : 𝓢(ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V, ℂ)) (v : Holomorphic.AntiOneSourcePair.HolomorphicAntiOneL2With V h),
    (ComplexMultiplication.HodgeComparison.SobolevIs.CM.Construction.sobolevL2Embedding (by norm_num : (0 : ℝ) ≤ 1) (Analysis.HodgeTheory.Decomposition.VectorCutoffOperator.Constructions.vectorSobolevCutoffCLM 1 g (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hsf (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h v)))) = ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g (HolomorphicFrame.Localization.holomorphicMetricFrameL2Localization V h e he i 1 f hf hsf ((h.antiOneL2Submodule V).subtypeL (HolomorphicSmooth.Green.holomorphicMetricSmoothGreen V h v)))

theorem holomorphicMetricSmoothGreen_cutoff_L2 (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicSmoothGreenCutoffL2 V h := by
  intro e he i f hf hsf g v
  exact
  Eq.trans (Analysis.HodgeTheory.Decomposition.VectorCutoffDifferential.Constructions.vectorSobolevCutoffCLM_embedding g (HolomorphicFrame.FrameLocalization.holomorphicMetricFrameH1Localization V h e he i f hf hsf (HolomorphicSmooth.Green.holomorphicMetricSmoothWeakSolution V h v)))
    (congrArg (ComplexMultiplication.HodgeComparison.CutoffDifferential.CM.Construction.schwartzL2Multiply g) (Mem.holomorphicMetricSmoothGreenH1Localization_L2 V h e he i f hf hsf v))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicGreen.Cutoff
