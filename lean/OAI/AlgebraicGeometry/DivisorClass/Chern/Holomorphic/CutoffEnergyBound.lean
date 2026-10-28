import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffIntegralBounds
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.EnergyMetric
import OAI.AlgebraicGeometry.DivisorClass.Chern.ThreeEnergyBound

/-! # Cutoff Energy Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern

noncomputable section

/-! Actual cutoff multiplication is bounded in the original joint Dolbeault energy norm. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicMetric.Data.HolomorphicLineMetricData.CutoffSmoothEnergyBound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_ : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (_ : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)),
    ∃ K : ℝ, 0 < K ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
      h.smoothOneEnergySq V (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a) ≤ K * h.smoothOneEnergySq V a

theorem HolomorphicMetric.Data.HolomorphicLineMetricData.cutoff_smoothOneEnergySq_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) :
    h.CutoffSmoothEnergyBound V := by
  intro e he i f hf hs
  have H := h.cutoff_operators_integral_bound V e he i f hf hs
  let C := H.choose
  let D := H.choose_spec.choose
  have hC := H.choose_spec.choose_spec.1
  have hD := H.choose_spec.choose_spec.2.1
  have hb := H.choose_spec.choose_spec.2.2
  have HN := h.smoothMul_integral_bound V f hf
  let M := HN.choose
  have hM := HN.choose_spec.1
  have hm := HN.choose_spec.2
  refine ⟨M + 2 * C + D, add_pos (add_pos hM (mul_pos (by norm_num) hC)) hD, fun a => ?_⟩
  exact ThreeEnergyBound.three_energy_component_bound M C D _ _ _ _ _ _ hM.le hC.le hD.le
    (h.formIntegralPair_nonneg V 1 a.val)
    (h.formIntegralPair_nonneg V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val)
    (h.formIntegralPair_nonneg V 0 (h.degreeCodifferential V 0 a.val))
    (hm 1 a.val) (hb a).1 (hb a).2

def Holomorphic.CutoffEnergyBound.HolomorphicCutoffEnergyBound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_ : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (_ : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ Holomorphic.CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)),
    ∃ K : ℝ, 0 < K ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
      ‖Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)‖ ^ 2 ≤
        K * ‖Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a‖ ^ 2

theorem Holomorphic.CutoffEnergyBound.holomorphicMetricCutoffEnergy_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u) :
    Holomorphic.CutoffEnergyBound.HolomorphicCutoffEnergyBound V h := by
  intro e he i f hf hs
  have H := h.cutoff_smoothOneEnergySq_bound V e he i f hf hs
  let K := H.choose
  have hK := H.choose_spec.1
  have hb := H.choose_spec.2
  refine ⟨K, hK, fun a => ?_⟩
  exact (HolomorphicSmooth.EnergyMetric.holomorphicMetricSmoothEnergyInclusion_norm_sq_metric V h (HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a)).trans_le
    ((hb a).trans_eq (congrArg (fun r : ℝ => K * r) (HolomorphicSmooth.EnergyMetric.holomorphicMetricSmoothEnergyInclusion_norm_sq_metric V h a).symm))

end

end OAI.AlgebraicGeometry.DivisorClass.Chern
