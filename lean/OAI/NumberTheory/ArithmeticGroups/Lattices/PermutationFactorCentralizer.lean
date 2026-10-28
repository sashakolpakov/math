import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperMatrixPermutationFactors
import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutedChamberApproximation
import OAI.NumberTheory.ArithmeticGroups.Lattices.SignedPermutationMatrices

/-! # Permutation Factor Centralizer -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationFactorCentralizer.Construction

noncomputable section

/-! The inverted factor centralizes a common chamber diagonal; the
preserved factor remains upper triangular after permutation. -/

open scoped Classical

theorem inversion_supported_matrix_commutes_diagonal {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : ∀ i j, ¬(i < j ∧ σ j < σ i) → (M - 1) i j = 0)
    (y : Fin n → ℝ) (hy : Monotone y) (hyσ : Monotone (y ∘ σ.symm)) :
    Commute M (Matrix.diagonal y) := by
  change M * Matrix.diagonal y = Matrix.diagonal y * M
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst j
    exact mul_comm _ _
  by_cases hp : i < j ∧ σ j < σ i
  · have he : y i = y j := PermutedChamberApproximation.Construction.monotone_permuted_inversion_equal σ.symm y hy hyσ i j hp.1.le hp.2.le
    rw [he, mul_comm]
  · have hz := hM i j hp
    simp only [Matrix.sub_apply, Matrix.one_apply_ne hij, sub_zero] at hz
    rw [hz, zero_mul, mul_zero]

theorem permutation_preserved_support_upper {n : ℕ} (σ : Equiv.Perm (Fin n))
    (M : Matrix (Fin n) (Fin n) ℝ) (hM : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular M)
    (hs : ∀ i j, ¬(i < j ∧ σ i < σ j) → (M - 1) i j = 0) :
    UpperUnitriangularMatrices.Construction.IsUpperUnitriangular ((σ⁻¹).permMatrix ℝ * M * σ.permMatrix ℝ) := by
  have he : (σ⁻¹).permMatrix ℝ * M * σ.permMatrix ℝ = M.submatrix σ.symm σ.symm := by
    ext i j
    simp [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rw [he]
  constructor
  · intro i j hij
    change j < i at hij
    have hp : ¬(σ.symm i < σ.symm j ∧ σ (σ.symm i) < σ (σ.symm j)) := by
      simpa only [Equiv.apply_symm_apply] using
        (show ¬(σ.symm i < σ.symm j ∧ i < j) from fun h => (not_lt_of_gt hij) h.2)
    have hz := hs (σ.symm i) (σ.symm j) hp
    have hne : σ.symm i ≠ σ.symm j := fun h => (ne_of_gt hij) (σ.symm.injective h)
    simpa only [Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, Matrix.submatrix_apply] using hz
  · intro i
    exact hM.2 (σ.symm i)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationFactorCentralizer.Construction
