import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.EnergyContinuousExt
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Energy Coercivity -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.EnergyCoercivity

noncomputable section

/-! The actual global smooth coercivity estimate extends to the closed smooth energy space with a strict source norm bound. -/

open scoped _root_.Manifold
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local instance] Holomorphic.EnergyContinuousExt.smoothCore_fullNormedSpace Holomorphic.EnergyContinuousExt.smoothCore_fullInnerProductSpace
  Holomorphic.EnergyContinuousExt.smoothCore_normedSpace Holomorphic.EnergyContinuousExt.smoothCore_innerProductSpace

variable (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
  {u : Holomorphic.Connecting.holomorphicUnitCohomology V.analyticModel V.analyticSpace} (h : HolomorphicMetric.Data.HolomorphicLineMetricData u)

/-- The original metric identifies the inclusion norm with its integral pairing. -/
def HolomorphicAntiOneNormFormula : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
    ‖Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a‖ ^ 2 = (h.formIntegralPair V 1 a.val a.val).re

theorem holomorphicMetricAntiOneInclusion_norm_sq : HolomorphicAntiOneNormFormula V h := by
  intro a
  change ‖(Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a).val‖ ^ 2 = _
  exact (congrArg (fun v : Holomorphic.IntegralPairZero.HolomorphicFormL2With V h 1 => ‖v‖ ^ 2)
    (Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion_val V h a)).trans (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V h 1 a.val)

/-- The smooth energy inclusion satisfies the original coercivity inequality. -/
def HolomorphicSmoothInclusionCoercive : Prop :=
  ∀ a : HolomorphicLine.AntiForms.HolomorphicLineAntiForm u ⊤ 1,
    ‖HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySource V h (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h a)‖ ^ 2 ≤
      ‖HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h a)‖ ^ 2 +
        ‖HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h a)‖ ^ 2

theorem holomorphicMetricOneEnergySmoothInclusion_coercive (hc : h.smoothDolbeaultOneCoercive V) :
    HolomorphicSmoothInclusionCoercive V h := by
  intro a
  change ‖Holomorphic.AntiOneSourcePair.holomorphicMetricAntiOneInclusion V h a‖ ^ 2 ≤
    ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val‖ ^ 2 +
      ‖Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion V h 0 (h.degreeCodifferential V 0 a.val)‖ ^ 2
  calc
    _ = (h.formIntegralPair V 1 a.val a.val).re := holomorphicMetricAntiOneInclusion_norm_sq V h a
    _ ≤ (h.formIntegralPair V 0 (h.degreeCodifferential V 0 a.val) (h.degreeCodifferential V 0 a.val)).re +
        (h.formIntegralPair V 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val).re :=
      h.smoothDolbeaultOneCoercive_energy V hc a
    _ = _ := (congrArg₂ (fun x y : ℝ => x + y)
      (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V h 0 (h.degreeCodifferential V 0 a.val)).symm
      (Holomorphic.IntegralPairZero.holomorphicFormL2WithInclusion_norm_sq V h 2 (HolomorphicLine.Dolbeault.holomorphicLineDolbeault u ⊤ 1 a).val).symm).trans (add_comm _ _)

private theorem holomorphicMetricSmoothEnergy_coercive (hc : h.smoothDolbeaultOneCoercive V)
    (v : Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h) :
    ‖Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v‖ ^ 2 ≤
      ‖HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h v.val‖ ^ 2 + ‖HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h v.val‖ ^ 2 :=
  EnergyCoercivity.energyCoercivity_on_range_closure (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySmoothInclusion V h)
    (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergySource V h) (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h)
    (HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h) (holomorphicMetricOneEnergySmoothInclusion_coercive V h hc) v.property

private theorem holomorphicMetricSmoothEnergySource_twice_sq (hc : h.smoothDolbeaultOneCoercive V)
    (v : Holomorphic.EnergyContinuousExt.HolomorphicSmoothOneEnergyWith V h) : 2 * ‖Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have he := JointClosedGraphEnergy.jointEnergy_norm_sq (h.closedDolbeaultOne V) (h.dolbeaultHilbertAdjoint V) (h.antiOneL2Submodule V).subtypeL v.val
  change ‖v‖ ^ 2 = ‖Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h v‖ ^ 2 +
    ‖HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyDerivative V h v.val‖ ^ 2 + ‖HolomorphicMetric.OneEnergy.holomorphicMetricOneEnergyAdjointValue V h v.val‖ ^ 2 at he
  have hh := holomorphicMetricSmoothEnergy_coercive V h hc v
  linarith only [he, hh]

/-- The smooth energy source has the prescribed strict operator-norm bound. -/
def HolomorphicSmoothEnergySourceNormBound : Prop :=
  ‖Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h‖ ≤ Real.sqrt (1 / 2)

theorem holomorphicMetricSmoothEnergySource_opNorm (hc : h.smoothDolbeaultOneCoercive V) :
    HolomorphicSmoothEnergySourceNormBound V h :=
  EnergyCoercivity.energySource_opNorm_of_twice_sq (Holomorphic.EnergyContinuousExt.holomorphicMetricSmoothEnergySource V h)
    (holomorphicMetricSmoothEnergySource_twice_sq V h hc)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.HolomorphicSmooth.EnergyCoercivity
