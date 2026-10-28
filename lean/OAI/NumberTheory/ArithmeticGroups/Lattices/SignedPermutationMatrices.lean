import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalOperatorMatrices
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # Signed Permutation Matrices -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.SignedPermutationMatrices.Construction

noncomputable section

/-! Signed permutation matrices are orthogonal normalizers of the
diagonal matrices. -/

open scoped Classical

def nonzeroDiagonalMatrixUnit {n : ℕ} (d : Fin n → ℝ) (hd : ∀ i, d i ≠ 0) :
    (Matrix (Fin n) (Fin n) ℝ)ˣ where
  val := Matrix.diagonal d
  inv := Matrix.diagonal (fun i => (d i)⁻¹)
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]
    simp [hd]

theorem signed_permutation_orthogonal {n : ℕ} (σ : Equiv.Perm (Fin n))
    (s : Fin n → ℝ) (hs : ∀ i, s i * s i = 1) :
    Matrix.diagonal s * σ.permMatrix ℝ ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  apply (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mpr
  have hp : σ.permMatrix ℝ * (σ.permMatrix ℝ).transpose = 1 := by
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
  calc
    Matrix.diagonal s * σ.permMatrix ℝ * ((σ.permMatrix ℝ).transpose * Matrix.diagonal s) =
        Matrix.diagonal s * (σ.permMatrix ℝ * (σ.permMatrix ℝ).transpose) * Matrix.diagonal s := by
      simp only [mul_assoc]
    _ = 1 := by rw [hp, mul_one, Matrix.diagonal_mul_diagonal]; simp [hs]

theorem permutation_support_diagonal_intertwining {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (hM : ∀ i j, j ≠ σ i → M i j = 0) (d : Fin n → ℝ) :
    M * Matrix.diagonal d = Matrix.diagonal (fun i => d (σ i)) * M := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : j = σ i
  · rw [h, mul_comm]
  · rw [hM i j h, zero_mul, mul_zero]

theorem signed_permutation_support {n : ℕ} (σ : Equiv.Perm (Fin n)) (s : Fin n → ℝ)
    (i j : Fin n) (hij : j ≠ σ i) :
    (Matrix.diagonal s * σ.permMatrix ℝ) i j = 0 := by
  simp [Matrix.diagonal_mul, Ne.symm hij]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.SignedPermutationMatrices.Construction
