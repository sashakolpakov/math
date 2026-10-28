import OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.WeightedBallBound
import OAI.AlgebraicGeometry.DivisorClass.Chern.CoordinateBallVolume

/-! # Log Point Estimate -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogPointEstimate

noncomputable section

/-! The squared value of a holomorphic function is O(ε) under the actual logarithmic point-weight bound. -/

open _root_.MeasureTheory _root_.Metric Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [MeasurableSpace E] [BorelSpace E]

theorem holomorphic_log_point_estimate (d : ℕ) (hd : Module.finrank ℝ E = 2 * d)
    (f : E → ℂ) {ε : ℝ} (hε : 0 < ε) (hf : DiffContOnCl ℂ f (ball 0 (Real.sqrt ε)))
    (C : ℝ) (hC : (∫ z in ball (0 : E) (Real.sqrt ε),
      RegularizedPointWeight.regularizedPointWeight (d + 1) ε z * ‖f z‖ ^ 2) ≤ C) :
    (volume : Measure E).real (ball (0 : E) 1) * ‖f 0‖ ^ 2 ≤ 2 ^ (d + 1) * ε * C := by
  have hb := (WeightedBallBound.holomorphic_weighted_ball_bound f (d + 1) hε hf).trans
    (mul_le_mul_of_nonneg_left hC (pow_nonneg (mul_nonneg (by norm_num) hε.le) _))
  rw [CoordinateBallVolume.coordinateBall_volume_sqrt d hd hε] at hb
  apply le_of_mul_le_mul_left (a := ε ^ d) _ (pow_pos hε d)
  calc
    ε ^ d * ((volume : Measure E).real (ball (0 : E) 1) * ‖f 0‖ ^ 2) =
        (ε ^ d * (volume : Measure E).real (ball (0 : E) 1)) * ‖f 0‖ ^ 2 := by ring
    _ ≤ (2 * ε) ^ (d + 1) * C := hb
    _ = ε ^ d * (2 ^ (d + 1) * ε * C) := by rw [mul_pow, pow_succ ε]; ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Holomorphic.LogPointEstimate
