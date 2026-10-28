import OAI.NumberTheory.Quaternion.Arithmetic.SplitMatrices

/-! # Split Inverse -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.SplitInverse

noncomputable section

/-! Explicit coordinates of the inverse quaternion splitting map. -/

open scoped Classical _root_.Quaternion
open QuaternionAlgebra _root_.Matrix

variable {K : Type*} [Field K] [CharZero K]

def quaternionSplitInverse (a b x y : K) (M : Matrix (Fin 2) (Fin 2) K) : ℍ[K,a,b] :=
  ⟨(M 0 0 + M 1 1) / 2, (M 0 1 + a * M 1 0) / (2 * a),
    (x * (M 0 0 - M 1 1) - y * (a * M 1 0 - M 0 1)) / (2 * b),
    (x * (a * M 1 0 - M 0 1) - a * y * (M 0 0 - M 1 1)) / (2 * a * b)⟩

theorem quaternionSplitInverse_apply (a b x y : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) (q : ℍ[K,a,b]) :
    quaternionSplitInverse a b x y (SplitMatrices.quaternionSplittingMap a b x y h q) = q := by
  rw [SplitMatrices.quaternionSplittingMap_apply]
  apply QuaternionAlgebra.ext
  · change (q.re + q.imJ * x + q.imK * a * y +
      (q.re - q.imJ * x - q.imK * a * y)) / 2 = q.re
    field_simp
    ring
  · change (a * q.imI - a * q.imJ * y - a * q.imK * x +
      a * (q.imI + q.imJ * y + q.imK * x)) / (2 * a) = q.imI
    field_simp
    ring
  · change (x * ((q.re + q.imJ * x + q.imK * a * y) -
      (q.re - q.imJ * x - q.imK * a * y)) -
      y * (a * (q.imI + q.imJ * y + q.imK * x) -
        (a * q.imI - a * q.imJ * y - a * q.imK * x))) / (2 * b) = q.imJ
    apply (div_eq_iff (mul_ne_zero two_ne_zero hb)).mpr
    linear_combination 2 * q.imJ * h
  · change (x * (a * (q.imI + q.imJ * y + q.imK * x) -
      (a * q.imI - a * q.imJ * y - a * q.imK * x)) -
      a * y * ((q.re + q.imJ * x + q.imK * a * y) -
        (q.re - q.imJ * x - q.imK * a * y))) / (2 * a * b) = q.imK
    apply (div_eq_iff (mul_ne_zero (mul_ne_zero two_ne_zero ha) hb)).mpr
    linear_combination 2 * a * q.imK * h

theorem quaternionSplittingEquiv_symm_apply (a b x y : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x ^ 2 - a * y ^ 2 = b) (M : Matrix (Fin 2) (Fin 2) K) :
    (SplitMatrices.quaternionSplittingEquiv a b x y ha hb h).symm M = quaternionSplitInverse a b x y M := by
  obtain ⟨q, rfl⟩ := (SplitMatrices.quaternionSplittingEquiv a b x y ha hb h).surjective M
  rw [AlgEquiv.symm_apply_apply]
  exact (quaternionSplitInverse_apply a b x y ha hb h q).symm

end

end OAI.NumberTheory.Quaternion.Arithmetic.SplitInverse
