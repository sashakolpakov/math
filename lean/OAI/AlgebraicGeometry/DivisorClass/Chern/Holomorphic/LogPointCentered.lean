import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogPointEstimate
import OAI.AlgebraicGeometry.DivisorClass.Chern.TranslateBallIntegral

/-! # Log Point Centered -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogPointCentered

noncomputable section

/-! The actual logarithmic point estimate at any coordinate center. -/

open _root_.MeasureTheory _root_.Metric Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem holomorphic_log_point_centered (d : ℕ) (hd : Module.finrank ℝ E = 2 * d)
    (x : E) (f : E → ℂ) {ε : ℝ} (hε : 0 < ε)
    (hf : DiffContOnCl ℂ f (ball x (Real.sqrt ε))) (C : ℝ)
    (hC : (∫ z in ball x (Real.sqrt ε), ((ε + ‖z - x‖ ^ 2) ^ (d + 1))⁻¹ * ‖f z‖ ^ 2) ≤ C) :
    (volume : Measure E).real (ball (0 : E) 1) * ‖f x‖ ^ 2 ≤ 2 ^ (d + 1) * ε * C := by
  have hR : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have hmap : MapsTo (fun z : E => x + z) (ball 0 (Real.sqrt ε)) (ball x (Real.sqrt ε)) := by
    intro z hz
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hg : DiffContOnCl ℂ (fun z => f (x + z)) (ball 0 (Real.sqrt ε)) := by
    have hadd : Differentiable ℂ (fun z : E => x + z) := differentiable_id.const_add x
    constructor
    · exact hf.1.comp hadd.differentiableOn hmap
    · apply hf.2.comp (continuous_const.add continuous_id).continuousOn
      intro z hz
      rw [closure_ball x hR.ne', closure_ball (0 : E) hR.ne'] at *
      change x + z ∈ closedBall x (Real.sqrt ε)
      simpa only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, sub_zero] using hz
  have hi : (∫ z in ball (0 : E) (Real.sqrt ε), RegularizedPointWeight.regularizedPointWeight (d + 1) ε z * ‖f (x + z)‖ ^ 2) ≤ C := by
    have ht := TranslateBallIntegral.translate_ball_integral x (Real.sqrt ε)
      (fun z => ((ε + ‖z - x‖ ^ 2) ^ (d + 1))⁻¹ * ‖f z‖ ^ 2)
    simpa only [add_sub_cancel_left, RegularizedPointWeight.regularizedPointWeight] using ht.trans_le hC
  simpa only [add_zero] using LogPointEstimate.holomorphic_log_point_estimate d hd (fun z => f (x + z)) hε hg C hi

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogPointCentered
