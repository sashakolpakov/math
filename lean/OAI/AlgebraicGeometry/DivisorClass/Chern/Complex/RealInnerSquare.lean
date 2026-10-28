import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-! # Real Inner Square -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.RealInnerSquare

noncomputable section

/-! The two original real inner products along a complex line recover the complex inner-product norm and its Cauchy--Schwarz bound. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
attribute [local instance] InnerProductSpace.complexToReal

theorem real_inner_rotation_sq (x v : E) :
    (inner ℝ x v) ^ 2 + (inner ℝ x (Complex.I • v)) ^ 2 = ‖inner ℂ x v‖ ^ 2 := by
  rw [real_inner_eq_re_inner ℂ, real_inner_eq_re_inner ℂ, inner_smul_right, Complex.sq_norm]
  change (inner ℂ x v).re ^ 2 + (Complex.I * inner ℂ x v).re ^ 2 = Complex.normSq (inner ℂ x v)
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
    Complex.normSq_apply, pow_two]
  ring

theorem real_inner_rotation_sq_le (x v : E) :
    (inner ℝ x v) ^ 2 + (inner ℝ x (Complex.I • v)) ^ 2 ≤ ‖x‖ ^ 2 * ‖v‖ ^ 2 := by
  rw [real_inner_rotation_sq]
  exact ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg x) (norm_nonneg v))).mpr
    (norm_inner_le_norm x v)).trans_eq (mul_pow ‖x‖ ‖v‖ 2)

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.Complex.RealInnerSquare
