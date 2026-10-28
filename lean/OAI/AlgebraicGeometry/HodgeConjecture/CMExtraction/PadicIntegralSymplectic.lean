import Mathlib

/-! # Padic Integral Symplectic -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralSymplectic.Local

noncomputable section

/-! Entrywise integral symplectic matrices and their inverses preserve
the actual q-adic phase-space unit lattice. -/

open scoped Classical _root_.Matrix

variable (q : ℕ) [Fact q.Prime]

theorem padic_matrix_mul_integral {I J K : Type*} [Fintype J]
    (A : Matrix I J ℚ_[q]) (B : Matrix J K ℚ_[q])
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ j k, ‖B j k‖ ≤ 1) :
    ∀ i k, ‖(A * B) i k‖ ≤ 1 := by
  intro i k
  change ‖∑ j, A i j * B j k‖ ≤ 1
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro j _
  rw [norm_mul]
  exact (mul_le_mul (hA i j) (hB j k) (norm_nonneg _) zero_le_one).trans (by simp)

theorem padic_matrix_mulVec_integral {I J : Type*} [Fintype J]
    (A : Matrix I J ℚ_[q]) (hA : ∀ i j, ‖A i j‖ ≤ 1)
    (x : J → ℚ_[q]) (hx : ∀ j, ‖x j‖ ≤ 1) : ∀ i, ‖A.mulVec x i‖ ≤ 1 := by
  intro i
  change ‖∑ j, A i j * x j‖ ≤ 1
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
  intro j _
  rw [norm_mul]
  exact (mul_le_mul (hA i j) (hx j) (norm_nonneg _) zero_le_one).trans (by simp)

theorem padic_J_integral (I : Type*) [DecidableEq I] :
    ∀ i j, ‖Matrix.J I ℚ_[q] i j‖ ≤ 1 := by
  intro i j
  cases i <;> cases j <;> simp [Matrix.J, Matrix.one_apply] <;> split_ifs <;> simp

theorem padic_symplectic_inverse_integral {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix.symplecticGroup I ℚ_[q]) (hS : ∀ i j, ‖S.val i j‖ ≤ 1) :
    ∀ i j, ‖(S⁻¹).val i j‖ ≤ 1 := by
  change ∀ i j, ‖((-Matrix.J I ℚ_[q]) * S.val.transpose * Matrix.J I ℚ_[q]) i j‖ ≤ 1
  apply padic_matrix_mul_integral q _ _ ?_ (padic_J_integral q I)
  apply padic_matrix_mul_integral q _ _ ?_ (fun i j => hS j i)
  intro i j
  simpa only [Matrix.neg_apply, norm_neg] using padic_J_integral q I i j

theorem padic_symplectic_integral_lattice_iff {I : Type*} [Fintype I] [DecidableEq I]
    (S : Matrix.symplecticGroup I ℚ_[q]) (hS : ∀ i j, ‖S.val i j‖ ≤ 1)
    (x : Sum I I → ℚ_[q]) :
    (∀ i, ‖(S⁻¹).val.mulVec x i‖ ≤ 1) ↔ ∀ i, ‖x i‖ ≤ 1 := by
  constructor
  · intro hx
    have hb := padic_matrix_mulVec_integral q S.val hS ((S⁻¹).val.mulVec x) hx
    have hc : S.val.mulVec ((S⁻¹).val.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, ← Submonoid.coe_mul, mul_inv_cancel,
        Submonoid.coe_one, Matrix.one_mulVec]
    simpa only [hc] using hb
  · exact padic_matrix_mulVec_integral q (S⁻¹).val (padic_symplectic_inverse_integral q S hS) x

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.PadicIntegralSymplectic.Local
