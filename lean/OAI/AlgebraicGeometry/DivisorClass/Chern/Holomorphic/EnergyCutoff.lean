import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffEnergyBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Equivalence

/-! # Energy Cutoff -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoff

noncomputable section

/-! Actual cutoff multiplication extends continuously to the native closed smooth energy space by its already proved energy bound. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

def holomorphicLineCutoffAntiLinear (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) :
    HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 :=
  ((SupportedForms.holomorphicLineSmoothMul u ⊤ 1 f hf).comp (HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 1).subtype).codRestrict
    (HolomorphicLine.AntiForms.holomorphicLineAntiFormSubmodule u ⊤ 1) (AntiMultiplication.holomorphicLineSmoothMul_anti u ⊤ f hf 1)

def holomorphicMetricSmoothCutoffEnergyLinear (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) :
    HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1 →ₗ[ℂ] EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h :=
  (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h).comp (holomorphicLineCutoffAntiLinear V u f hf)

private theorem holomorphicMetricSmoothCutoffEnergyLinear_apply (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    holomorphicMetricSmoothCutoffEnergyLinear V h f hf a =
      EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a) := rfl

private theorem holomorphicMetricSmoothCutoffEnergyLinear_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (he : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)) :
    ∃ C : ℝ, ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
      ‖holomorphicMetricSmoothCutoffEnergyLinear V h f hf a‖ ≤ C * ‖EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a‖ := by
  have H := CutoffEnergyBound.holomorphicMetricCutoffEnergy_bound V h e he i f hf hs
  let K := H.choose
  have hK := H.choose_spec.1
  have hb := H.choose_spec.2
  refine ⟨Real.sqrt K, fun a => ?_⟩
  have hbound := HolomorphicMetric.Equivalence.nonneg_le_sqrt_mul_of_sq_le (norm_nonneg _) (norm_nonneg _) hK.le (hb a)
  exact (congrArg norm (holomorphicMetricSmoothCutoffEnergyLinear_apply V h f hf a)).trans_le hbound

def holomorphicMetricSmoothEnergyCutoff (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f) :
    EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h →L[ℂ] EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h :=
  (holomorphicMetricSmoothCutoffEnergyLinear V h f hf).extendOfNorm (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h)

def HolomorphicSmoothEnergyCutoffOnSmooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_ : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace) (f : V.analyticSpace → ℂ)
    (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (_ : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace))
    (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
    holomorphicMetricSmoothEnergyCutoff V h f hf (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a) =
      EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)

theorem holomorphicMetricSmoothEnergyCutoff_on_smooth (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicSmoothEnergyCutoffOnSmooth V h := by
  intro e he i f hf hs a
  have hp := LinearMap.extendOfNorm_eq (EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion_dense V h)
    (holomorphicMetricSmoothCutoffEnergyLinear_bound V h e he i f hf hs) a
  exact hp.trans (holomorphicMetricSmoothCutoffEnergyLinear_apply V h f hf a)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyCutoff
