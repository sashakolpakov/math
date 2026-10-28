import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogWeight
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! # Regularized Log Differential -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogDifferential

noncomputable section

/-! Explicit first derivatives of the actual regularized logarithmic point potential. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem regularizedNormSquare_hasFDerivAt (x z : E) (ε : ℝ) :
    HasFDerivAt (fun y : E => ε + ‖y - x‖ ^ 2) (2 • innerSL ℝ (z - x)) z := by
  simpa only [ContinuousLinearMap.comp_id, id_eq] using
    (((hasFDerivAt_id z).sub_const x).norm_sq.const_add ε)

theorem regularizedNegativeLog_hasFDerivAt (x : E) (m : ℕ) {ε : ℝ} (hε : 0 < ε) (z : E) :
    HasFDerivAt (RegularizedLogWeight.regularizedNegativeLog x m ε)
      ((-(m : ℝ)) • ((ε + ‖z - x‖ ^ 2)⁻¹ • (2 • innerSL ℝ (z - x)))) z :=
  ((regularizedNormSquare_hasFDerivAt x z ε).log
    (ne_of_gt (add_pos_of_pos_of_nonneg hε (sq_nonneg ‖z - x‖)))).const_mul (-(m : ℝ))

theorem regularizedNegativeLog_fderiv_apply (x : E) (m : ℕ) {ε : ℝ} (hε : 0 < ε) (z v : E) :
    fderiv ℝ (RegularizedLogWeight.regularizedNegativeLog x m ε) z v =
      -(2 * (m : ℝ)) * inner ℝ (z - x) v / (ε + ‖z - x‖ ^ 2) := by
  rw [(regularizedNegativeLog_hasFDerivAt x m hε z).fderiv]
  simp only [_root_.smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogDifferential
