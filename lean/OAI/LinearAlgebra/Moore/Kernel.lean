import OAI.LinearAlgebra.Moore.Basic

/-! Singularity of the signed Moore determinant from a quaternionic null vector. -/

namespace OAI.LinearAlgebra.Moore

open Matrix

/-- A normalized null vector yields a singular congruence projection fixing
the Hermitian matrix, so its Moore determinant vanishes. -/
theorem mooreDet_zero_of_normalized_kernel (n : ℕ)
    (H : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hH : H.IsHermitian)
    (v : Fin n → Quaternion ℝ) (k : Fin n) (hvk : v k = 1)
    (hv : H *ᵥ v = 0) : mooreDet n H = 0 := by
  let e : Fin n → Quaternion ℝ := Pi.single k 1
  let R : Matrix (Fin n) (Fin n) (Quaternion ℝ) := 1 - vecMulVec v e
  have hHeq : Hᴴ = H := hH
  have hright : H * R = H := by
    dsimp only [R]
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_vecMulVec, hv]
    simp
  have hleft : Rᴴ * H = H := by
    simpa only [Matrix.conjTranspose_mul, hHeq] using congrArg Matrix.conjTranspose hright
  have hcong : Rᴴ * H * (Rᴴ)ᴴ = H := by
    rw [Matrix.conjTranspose_conjTranspose, hleft, hright]
  have hdet : (complexify R).det = 0 := by
    apply Matrix.det_eq_zero_of_row_eq_zero (k, 0)
    rintro ⟨j, b⟩
    have hrow : R k j = 0 := by
      simp [R, e, Matrix.one_apply, vecMulVec_apply, hvk, Pi.single_apply, eq_comm]
    change quaternionMatrix (R k j) 0 b = 0
    rw [hrow, quaternionMatrix_zero]
    rfl
  have h := mooreDet_congruence n H Rᴴ
  rw [hcong, complexify_star, Matrix.det_conjTranspose, hdet] at h
  simpa using h

/-- A nonzero right-null vector forces the signed Moore determinant of a
Hermitian quaternionic matrix to vanish, in every finite dimension. -/
theorem mooreDet_zero_of_kernel (n : ℕ)
    (H : Matrix (Fin n) (Fin n) (Quaternion ℝ)) (hH : H.IsHermitian)
    (v : Fin n → Quaternion ℝ) (hv : H *ᵥ v = 0) (hne : v ≠ 0) :
    mooreDet n H = 0 := by
  have hex : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    funext k
    exact h k
  obtain ⟨k, hk⟩ := hex
  let w : Fin n → Quaternion ℝ := fun j => v j * (v k)⁻¹
  have hwk : w k = 1 := mul_inv_cancel₀ hk
  have hw : H *ᵥ w = 0 := by
    funext j
    change (∑ i, H j i * (v i * (v k)⁻¹)) = 0
    simp only [← mul_assoc, ← Finset.sum_mul]
    change (H *ᵥ v) j * (v k)⁻¹ = 0
    rw [hv]
    simp
  exact mooreDet_zero_of_normalized_kernel n H hH w k hwk hw

end OAI.LinearAlgebra.Moore
