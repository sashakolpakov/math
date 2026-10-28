import Mathlib

/-! # Orthogonal Vector -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.OrthogonalVector

noncomputable section

/-! In a nondegenerate ternary diagonal quadratic space, every
orthogonal plane contains a vector of nonzero quadratic value. The
explicit vectors will conjugate a quaternion to its canonical conjugate. -/

open scoped Classical

variable {F : Type*} [Field F] [CharZero F]

theorem quaternion_exists_orthogonal_nonzero_norm (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (x y z : F) :
    ∃ s t u : F, a * x * s + b * y * t - a * b * z * u = 0 ∧
      -a * s ^ 2 - b * t ^ 2 + a * b * u ^ 2 ≠ 0 := by
  by_cases hx : x = 0
  · refine ⟨1, 0, 0, by simp [hx], ?_⟩
    simpa only [one_pow, mul_one, zero_pow (by omega : 2 ≠ 0), mul_zero, sub_zero, add_zero]
      using neg_ne_zero.mpr ha
  by_contra h
  push Not at h
  have h₁ := h (b * y) (-a * x) 0 (by ring)
  have h₂ := h (b * z) 0 x (by ring)
  have h₃ := h (b * y + b * z) (-a * x) x (by ring)
  have hcross : (2 * a * b ^ 2) * (y * z) = 0 := by
    linear_combination h₁ + h₂ - h₃
  have hfactor : 2 * a * b ^ 2 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero _ hb)
  have hyz : y * z = 0 := (mul_eq_zero.mp hcross).resolve_left hfactor
  rcases mul_eq_zero.mp hyz with hy | hz
  · have he : a ^ 2 * b * x ^ 2 = 0 := by
      rw [hy] at h₁
      linear_combination -h₁
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ ha) hb) (pow_ne_zero _ hx) he
  · have he : a * b * x ^ 2 = 0 := by
      rw [hz] at h₂
      linear_combination h₂
    exact mul_ne_zero (mul_ne_zero ha hb) (pow_ne_zero _ hx) he

end

end OAI.NumberTheory.Quaternion.Arithmetic.OrthogonalVector
