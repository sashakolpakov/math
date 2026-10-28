import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogHessian
import OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.RealInnerSquare

/-! # Regularized Log Levi -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogLevi

noncomputable section

/-! The actual regularized negative logarithmic potential has nonpositive complex-line Hessian. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
attribute [local instance] InnerProductSpace.complexToReal

theorem regularizedNegativeLog_levi_nonpos (x : E) (m : ℕ) {ε : ℝ} (hε : 0 < ε) (z v : E) :
    fderiv ℝ (fun y => fderiv ℝ (RegularizedLogWeight.regularizedNegativeLog x m ε) y v) z v +
      fderiv ℝ (fun y => fderiv ℝ (RegularizedLogWeight.regularizedNegativeLog x m ε) y (Complex.I • v)) z (Complex.I • v) ≤ 0 := by
  rw [RegularizedLogHessian.regularizedNegativeLog_second_apply x m hε, RegularizedLogHessian.regularizedNegativeLog_second_apply x m hε,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  have hIv : ‖Complex.I • v‖ = ‖v‖ := by rw [norm_smul, Complex.norm_I, one_mul]
  rw [hIv]
  have hq : 0 < ε + ‖z - x‖ ^ 2 := add_pos_of_pos_of_nonneg hε (sq_nonneg ‖z - x‖)
  have hnum : (inner ℝ (z - x) v) ^ 2 + (inner ℝ (z - x) (Complex.I • v)) ^ 2 -
      (ε + ‖z - x‖ ^ 2) * ‖v‖ ^ 2 ≤ 0 := by
    nlinarith only [Chern.Complex.RealInnerSquare.real_inner_rotation_sq_le (z - x) v, mul_nonneg hε.le (sq_nonneg ‖v‖)]
  have hb := mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (show 0 ≤ 4 * (m : ℝ) by positivity) (sq_nonneg (ε + ‖z - x‖ ^ 2))) hnum
  calc
    _ = (4 * (m : ℝ) / (ε + ‖z - x‖ ^ 2) ^ 2) *
        ((inner ℝ (z - x) v) ^ 2 + (inner ℝ (z - x) (Complex.I • v)) ^ 2 -
          (ε + ‖z - x‖ ^ 2) * ‖v‖ ^ 2) := by
      field_simp [ne_of_gt hq]
      ring
    _ ≤ 0 := hb

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogLevi
