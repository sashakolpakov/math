import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogDifferential
import Mathlib.Analysis.Calculus.Deriv.Inv

/-! # Regularized Log Hessian -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogHessian

noncomputable section

/-! Explicit actual second derivatives of the smooth logarithmic point potential. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem realInner_sub_hasFDerivAt (x z v : E) :
    HasFDerivAt (fun y => inner ℝ (y - x) v) (innerSL ℝ v) z := by
  simpa only [ContinuousLinearMap.comp_id, Function.comp_def, innerSL_apply_apply, real_inner_comm, id_eq] using!
    ((innerSL ℝ v).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))

theorem regularizedNegativeLog_directional_hasFDerivAt (x : E) (m : ℕ) {ε : ℝ} (hε : 0 < ε) (z v : E) :
    HasFDerivAt (fun y => fderiv ℝ (RegularizedLogWeight.regularizedNegativeLog x m ε) y v)
      (-(2 * (m : ℝ)) •
        (inner ℝ (z - x) v • (-((ε + ‖z - x‖ ^ 2) ^ 2)⁻¹ • (2 • innerSL ℝ (z - x))) +
          (ε + ‖z - x‖ ^ 2)⁻¹ • innerSL ℝ v)) z := by
  have hi := (hasDerivAt_inv (ne_of_gt (add_pos_of_pos_of_nonneg hε (sq_nonneg ‖z - x‖)))).comp_hasFDerivAt z
    (RegularizedLogDifferential.regularizedNormSquare_hasFDerivAt x z ε)
  have hp := ((realInner_sub_hasFDerivAt x z v).mul hi).const_mul (-(2 * (m : ℝ)))
  have heq : (fun y => fderiv ℝ (RegularizedLogWeight.regularizedNegativeLog x m ε) y v) =
      (fun y => -(2 * (m : ℝ)) * (inner ℝ (y - x) v * (ε + ‖y - x‖ ^ 2)⁻¹)) := by
    funext y
    rw [RegularizedLogDifferential.regularizedNegativeLog_fderiv_apply x m hε y v]
    ring
  rw [heq]
  exact hp

theorem regularizedNegativeLog_second_apply (x : E) (m : ℕ) {ε : ℝ} (hε : 0 < ε) (z v w : E) :
    fderiv ℝ (fun y => fderiv ℝ (RegularizedLogWeight.regularizedNegativeLog x m ε) y v) z w =
      -(2 * (m : ℝ)) * inner ℝ v w / (ε + ‖z - x‖ ^ 2) +
        (4 * (m : ℝ)) * inner ℝ (z - x) v * inner ℝ (z - x) w / (ε + ‖z - x‖ ^ 2) ^ 2 := by
  rw [(regularizedNegativeLog_directional_hasFDerivAt x m hε z v).fderiv]
  simp only [_root_.smul_apply, _root_.add_apply, innerSL_apply_apply, smul_eq_mul]
  ring

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogHessian
