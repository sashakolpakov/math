import Mathlib

/-! # Intrinsic Inverse Pullback -/

namespace OAI.RepresentationTheory.Theta.Kernel.IntrinsicInversePullback.Intrinsic

noncomputable section

/-! Inverse bilinear-form transport with possibly different finite
coordinate index types. This is the algebra used for theta completion. -/

open scoped Classical _root_.Matrix

variable {k I J : Type} [Field k] [Fintype I] [Fintype J]
variable [DecidableEq I] [DecidableEq J]

theorem inverse_congruence (R : Matrix J I k) (S : Matrix I J k)
    (X : Matrix I I k) (Y : Matrix J J k)
    (hRS : R * S = 1) (hX : IsUnit X.det) (hY : IsUnit Y.det)
    (hpull : Rᵀ * Y * R = X) : Y⁻¹ = R * X⁻¹ * Rᵀ := by
  have ht : Sᵀ * Rᵀ = 1 := by rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one]
  have hYR : Y * R = Sᵀ * X := by
    calc
      Y * R = (Sᵀ * Rᵀ) * (Y * R) := by rw [ht, Matrix.one_mul]
      _ = Sᵀ * (Rᵀ * Y * R) := by simp only [Matrix.mul_assoc]
      _ = Sᵀ * X := by rw [hpull]
  have hprod : Y * (R * X⁻¹ * Rᵀ) = 1 := by
    calc
      Y * (R * X⁻¹ * Rᵀ) = (Y * R) * X⁻¹ * Rᵀ := by simp only [Matrix.mul_assoc]
      _ = (Sᵀ * X) * X⁻¹ * Rᵀ := by rw [hYR]
      _ = Sᵀ * (X * X⁻¹) * Rᵀ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv X hX, Matrix.mul_one, ht]
  calc
    Y⁻¹ = Y⁻¹ * (Y * (R * X⁻¹ * Rᵀ)) := by rw [hprod, Matrix.mul_one]
    _ = (Y⁻¹ * Y) * (R * X⁻¹ * Rᵀ) := by simp only [Matrix.mul_assoc]
    _ = R * X⁻¹ * Rᵀ := by rw [Matrix.nonsing_inv_mul Y hY, Matrix.one_mul]

theorem inverse_quadratic_pullback (R : Matrix J I k) (X : Matrix I I k) (Y : Matrix J J k)
    (hInv : Y⁻¹ = R * X⁻¹ * Rᵀ) (ξ : J → k) :
    ξ ⬝ᵥ (Y⁻¹.mulVec ξ) = (Rᵀ.mulVec ξ) ⬝ᵥ (X⁻¹.mulVec (Rᵀ.mulVec ξ)) := by
  rw [hInv, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have he : ξ ᵥ* R = Rᵀ.mulVec ξ := by
    simpa only [Matrix.transpose_transpose] using Matrix.vecMul_transpose Rᵀ ξ
  rw [he]

end

end OAI.RepresentationTheory.Theta.Kernel.IntrinsicInversePullback.Intrinsic
