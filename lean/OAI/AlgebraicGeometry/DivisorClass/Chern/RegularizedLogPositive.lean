import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogLevi
import OAI.AlgebraicGeometry.DivisorClass.Chern.RealScalarCurvatureHessian

/-! # Regularized Log Positive -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogPositive

noncomputable section

/-! The literal Chern curvature of the regularized negative logarithmic scalar potential is semipositive with the original I normalization. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
attribute [local instance] InnerProductSpace.complexToReal

theorem regularizedNegativeLog_chern_nonneg (x : E) (m : ℕ) {ε : ℝ} (hε : 0 < ε) (z v : E) :
    0 ≤ (Complex.I * extDeriv (fun y => RealScalarOperator.realScalarChernOperator E
      (fderiv ℝ (RegularizedLogWeight.regularizedNegativeLog x m ε) y)) z ![v, Complex.I • v]).re := by
  rw [RealScalarCurvatureHessian.realScalarChern_curvature_hessian _ (RegularizedLogWeight.regularizedNegativeLog_smooth x m hε)]
  exact mul_nonneg_of_nonpos_of_nonpos (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    (RegularizedLogLevi.regularizedNegativeLog_levi_nonpos x m hε z v)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogPositive
