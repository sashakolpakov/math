import OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.EnergyCoercivity

/-! # Energy Metric -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.EnergyMetric

noncomputable section

/-! The original joint Hilbert energy norm is the sum of the three original smooth metric pairings. -/

open _root_.TopologicalSpace
open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data.HolomorphicLineMetricData.smoothOneEnergySq (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) : ℝ :=
  (h.formIntegralPair V 1 a.val a.val).re +
    (h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val).re +
      (h.formIntegralPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 a.val)).re

private theorem holomorphicMetricOneEnergySmoothInclusion_norm_sq_metric (a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1) :
    ‖HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h a‖ ^ 2 = h.smoothOneEnergySq V a := by
  have he := JointClosedGraphEnergy.jointEnergy_norm_sq (h.closedDolbeaultOne V) (h.dolbeaultHilbertAdjoint V) (h.antiOneL2Submodule V).subtypeL (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h a)
  change ‖HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h a‖ ^ 2 = ‖Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a‖ ^ 2 +
    ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val‖ ^ 2 +
      ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 a.val)‖ ^ 2 at he
  exact he.trans (congrArg₂ (fun r s : ℝ => r + s)
    (congrArg₂ (fun r s : ℝ => r + s) (EnergyCoercivity.holomorphicMetricAntiOneInclusion_norm_sq V h a)
      (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val))
    (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V h 0 (h.degreeCodifferential V 0 a.val)))

/-- The smooth energy inclusion realizes the sum of the three metric pairings. -/
def HolomorphicSmoothEnergyMetricFormula : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
    ‖Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergyInclusion V h a‖ ^ 2 = h.smoothOneEnergySq V a

theorem holomorphicMetricSmoothEnergyInclusion_norm_sq_metric :
    HolomorphicSmoothEnergyMetricFormula V h :=
  holomorphicMetricOneEnergySmoothInclusion_norm_sq_metric V h

/-- The full smooth energy bounds its source pairing. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data.HolomorphicLineMetricData.SmoothEnergySourceBound : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
    (h.formIntegralPair V 1 a.val a.val).re ≤ h.smoothOneEnergySq V a

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data.HolomorphicLineMetricData.smoothOneEnergySq_source_le :
    h.SmoothEnergySourceBound V := by
  intro a
  have hd := h.formIntegralPair_nonneg V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val
  have hs := h.formIntegralPair_nonneg V 0 (h.degreeCodifferential V 0 a.val)
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.smoothOneEnergySq
  linarith only [hd, hs]

/-- The full smooth energy bounds the smooth Laplacian pairing. -/
def _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data.HolomorphicLineMetricData.SmoothEnergyLaplacianBound : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
    (h.formIntegralPair V 1 (h.smoothDolbeaultLaplacianOne V a) a.val).re ≤ h.smoothOneEnergySq V a

theorem _root_.OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicMetric.Data.HolomorphicLineMetricData.smoothOneEnergySq_laplacian_le :
    h.SmoothEnergyLaplacianBound V := by
  intro a
  have hp := (congrArg Complex.re (h.smoothDolbeaultLaplacianOne_pair V a a)).trans (Complex.add_re _ _)
  have hn := h.formIntegralPair_nonneg V 1 a.val
  unfold HolomorphicMetric.Data.HolomorphicLineMetricData.smoothOneEnergySq
  linarith only [hp, hn]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.EnergyMetric
