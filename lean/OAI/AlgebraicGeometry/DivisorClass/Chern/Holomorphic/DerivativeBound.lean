import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.CutoffEnergyBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicCompact.Derivative

/-! # Derivative Bound -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DerivativeBound

noncomputable section

/-! Local ordinary derivatives of original smooth forms are bounded by their native joint energy norm. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold ContDiff
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] EnergyContinuousExt.smoothCore_fullNormedSpace EnergyContinuousExt.smoothCore_fullInnerProductSpace
  EnergyContinuousExt.smoothCore_normedSpace EnergyContinuousExt.smoothCore_innerProductSpace

def HolomorphicCompactDerivativeEnergyBound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_ : e ∈ atlas V.analyticModel V.analyticSpace)
  (i : V.analyticSpace)
  (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
  (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)),
    ∃ K : ℝ, 0 < K ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) (v : ComplexMultiplication.HodgeComparison.EuclideanMetric.CM.Construction.varietyEuclideanModel V), ‖v‖ = 1 →
      Projective.DerivativeIntegralBound.projectiveFieldDirectionalIntegral V 1 (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) v ≤
        K * ‖EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a‖ ^ 2

theorem holomorphicMetricCompactDerivative_energy_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicCompactDerivativeEnergyBound V h := by
  intro e he i f hf hs
  have H := h.compactOrdinaryDerivative_bound V e he i f hf hs
  let C := H.choose
  let D := H.choose_spec.choose
  have hC := H.choose_spec.choose_spec.1
  have hD := H.choose_spec.choose_spec.2.1
  have hb := H.choose_spec.choose_spec.2.2
  have HM := h.cutoff_smoothOneEnergySq_bound V e he i f hf hs
  let M := HM.choose
  have hM := HM.choose_spec.1
  have hm := HM.choose_spec.2
  refine ⟨(C + D) * M, mul_pos (add_pos hC hD) hM, fun a v hv => ?_⟩
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  have hsum := add_le_add (mul_le_mul_of_nonneg_left (h.smoothOneEnergySq_laplacian_le V A) hC.le)
    (mul_le_mul_of_nonneg_left (h.smoothOneEnergySq_source_le V A) hD.le)
  have hi : Projective.DerivativeIntegralBound.projectiveFieldDirectionalIntegral V 1 (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) v ≤
      (C + D) * h.smoothOneEnergySq V A :=
    (hb a v hv).trans (hsum.trans_eq (add_mul C D (h.smoothOneEnergySq V A)).symm)
  calc
    _ ≤ (C + D) * (M * h.smoothOneEnergySq V a) :=
      hi.trans (mul_le_mul_of_nonneg_left (hm a) (add_pos hC hD).le)
    _ = ((C + D) * M) * h.smoothOneEnergySq V a := (mul_assoc _ _ _).symm
    _ = _ := congrArg (fun r : ℝ => ((C + D) * M) * r)
      (HolomorphicSmooth.EnergyMetric.holomorphicMetricSmoothEnergyInclusion_norm_sq_metric V h a).symm

def HolomorphicCompactFieldEnergyBound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 : Prop :=
  ∀ (e : OpenPartialHomeomorph V.analyticSpace V.analyticModel) (_ : e ∈ atlas V.analyticModel V.analyticSpace)
    (i : V.analyticSpace)
    (f : V.analyticSpace → ℂ) (hf : ContMDiff 𝓘(ℝ, V.analyticModel) 𝓘(ℝ, ℂ) ∞ f)
    (hs : tsupport f ⊆ (Analysis.DifferentialForms.Manifold.ChartEquiv.chartSourceOpen e ⊓ CohomologyTransitions.holomorphicCohomologyDomain V.analyticModel V.analyticSpace u i : Opens V.analyticSpace)),
    ∃ K : ℝ, 0 < K ∧ ∀ (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1),
      Projective.DerivativeIntegralBound.projectiveFieldNormIntegral V 1 (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) ≤
        K * ‖EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a‖ ^ 2

theorem holomorphicMetricCompactField_energy_bound (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    {u : Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)
 :
    HolomorphicCompactFieldEnergyBound V h := by
  intro e he i f hf hs
  have H := h.compactFieldNorm_bound V e he i f hf hs
  let C := H.choose
  have hC := H.choose_spec.1
  have hb := H.choose_spec.2
  have HM := h.cutoff_smoothOneEnergySq_bound V e he i f hf hs
  let M := HM.choose
  have hM := HM.choose_spec.1
  have hm := HM.choose_spec.2
  refine ⟨C * M, mul_pos hC hM, fun a => ?_⟩
  let A := HolomorphicCompact.Bochner.holomorphicLineCutoffAntiForm V f hf a
  have hi : Projective.DerivativeIntegralBound.projectiveFieldNormIntegral V 1 (HolomorphicCompact.ChartField.holomorphicLineCompactChartField V e i 1 f hf hs a.val) ≤
      C * h.smoothOneEnergySq V A :=
    (hb a.val).trans (mul_le_mul_of_nonneg_left (h.smoothOneEnergySq_source_le V A) hC.le)
  calc
    _ ≤ C * (M * h.smoothOneEnergySq V a) := hi.trans (mul_le_mul_of_nonneg_left (hm a) hC.le)
    _ = (C * M) * h.smoothOneEnergySq V a := (mul_assoc _ _ _).symm
    _ = _ := congrArg (fun r : ℝ => (C * M) * r) (HolomorphicSmooth.EnergyMetric.holomorphicMetricSmoothEnergyInclusion_norm_sq_metric V h a).symm

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.DerivativeBound
