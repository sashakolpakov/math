import OAI.NumberTheory.ArithmeticGroups.Lattices.SignedPermutationMatrices

/-! # Permutation Matrix Units -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationMatrixUnits.Construction

noncomputable section

/-! Permutation matrices as units, including their action on diagonals. -/

open scoped Classical

def permutationMatrixUnit {n : ℕ} (σ : Equiv.Perm (Fin n)) : (Matrix (Fin n) (Fin n) ℝ)ˣ where
  val := σ.permMatrix ℝ
  inv := (σ⁻¹).permMatrix ℝ
  val_inv := by rw [← Matrix.permMatrix_mul, inv_mul_cancel, Matrix.permMatrix_one]
  inv_val := by rw [← Matrix.permMatrix_mul, mul_inv_cancel, Matrix.permMatrix_one]

theorem permutationMatrixUnit_orthogonal {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (permutationMatrixUnit σ).val ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
  simpa only [Matrix.diagonal_one, one_mul] using! SignedPermutationMatrices.Construction.signed_permutation_orthogonal σ
    (fun _ => 1) (fun _ => one_mul 1)

theorem permutationMatrixUnit_conjugate_diagonal {n : ℕ} (σ : Equiv.Perm (Fin n))
    (d : Fin n → ℝ) :
    (permutationMatrixUnit σ)⁻¹.val * Matrix.diagonal d * (permutationMatrixUnit σ).val =
      Matrix.diagonal (fun i => d (σ.symm i)) := by
  change (σ⁻¹).permMatrix ℝ * Matrix.diagonal d * σ.permMatrix ℝ = _
  ext i j
  simp only [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_apply]
  by_cases hij : i = j
  · subst j
    simp
  · have hne : σ.symm i ≠ σ.symm j := fun h => hij (σ.symm.injective h)
    simp [Matrix.diagonal_apply_ne _ hne, Matrix.diagonal_apply_ne _ hij]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationMatrixUnits.Construction
