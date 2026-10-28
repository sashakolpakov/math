import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperMonomialElimination
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # Matrix Bruhat Decomposition -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixBruhatDecomposition.Construction

noncomputable section

/-! Bruhat decomposition for real general linear matrices, with
upper unitriangular factors and a nonzero diagonal. -/

open scoped Classical

theorem permutation_support_eq_diagonal_mul {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ) (σ : Equiv.Perm (Fin n))
    (hM : ∀ i j, j ≠ σ i → M i j = 0) :
    M = Matrix.diagonal (fun i => M i (σ i)) * σ.permMatrix ℝ := by
  ext i j
  rw [Matrix.diagonal_mul]
  by_cases h : j = σ i
  · subst j
    simp
  · simp [hM i j h, Ne.symm h]

theorem exists_matrix_bruhat_decomposition {n : ℕ} (M : (Matrix (Fin n) (Fin n) ℝ)ˣ) :
    ∃ U V : (Matrix (Fin n) (Fin n) ℝ)ˣ, ∃ d : Fin n → ℝ, ∃ σ : Equiv.Perm (Fin n),
      UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U.val ∧ UpperUnitriangularMatrices.Construction.IsUpperUnitriangular V.val ∧ (∀ i, d i ≠ 0) ∧
      M.val = U.val * Matrix.diagonal d * σ.permMatrix ℝ * V.val := by
  obtain ⟨U, V, σ, hU, hV, hs⟩ := UpperMonomialElimination.Construction.exists_upper_monomial_elimination n M
  let u := hU.isUnit.unit
  let v := hV.isUnit.unit
  let r := u * M * v
  have hu : u.val = U := hU.isUnit.unit_spec
  have hv : v.val = V := hV.isUnit.unit_spec
  have hr : r.val = U * M.val * V := by
    change u.val * M.val * v.val = _
    rw [hu, hv]
  have hrs : ∀ i j, j ≠ σ i → r.val i j = 0 := by
    rw [hr]
    exact hs
  let d := fun i => r.val i (σ i)
  have hd : ∀ i, d i ≠ 0 := by
    intro i
    obtain ⟨j, hj⟩ := Split.ExponentialMatrixChamber.Construction.invertible_matrix_row_nonzero r i
    have he : j = σ i := by
      by_contra hn
      exact hj (hrs i j hn)
    simpa only [he] using hj
  have he : r.val = Matrix.diagonal d * σ.permMatrix ℝ :=
    permutation_support_eq_diagonal_mul r.val σ hrs
  refine ⟨u⁻¹, v⁻¹, d, σ, hU.unit_inv u, hV.unit_inv v, hd, ?_⟩
  have hM : M = u⁻¹ * r * v⁻¹ := by dsimp only [r]; group
  have hval := congrArg Units.val hM
  change M.val = (u⁻¹).val * r.val * (v⁻¹).val at hval
  rw [he, ← mul_assoc] at hval
  exact hval

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixBruhatDecomposition.Construction
