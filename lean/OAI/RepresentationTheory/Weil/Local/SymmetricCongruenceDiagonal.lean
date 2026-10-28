import OAI.RepresentationTheory.Weil.Local.SiegelGaussian
import OAI.RepresentationTheory.Weil.Local.DiagonalAlgebra
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # Symmetric Congruence Diagonal -/

namespace OAI.RepresentationTheory.Weil.Local.SymmetricCongruenceDiagonal.Construction

noncomputable section

/-! Congruence diagonalization of a nonsingular symmetric matrix over the local base field. -/

open _root_.Matrix _root_.Module

variable {k : Type} [Field k] [CharZero k] {n : ℕ}

theorem symmetric_generalLinear_congruence_diagonal
    (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) :
    ∃ (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ),
      A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val) := by
  let : Invertible (2 : k) := invertibleOfNonzero (by norm_num)
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis (K := k) (V := FunctionsMetaplectic.Construction.Position k n)
    (B := M.val.toBilin')
    (LinearMap.BilinForm.isSymm_iff.mp (Matrix.isSymm_toBilin'_iff_isSymm.mpr hM))
  let e' : Fin (finrank k (FunctionsMetaplectic.Construction.Position k n)) ≃ Fin n := finCongr (by simp [FunctionsMetaplectic.Construction.Position])
  let b : Basis (Fin n) k (FunctionsMetaplectic.Construction.Position k n) := v.reindex e'
  have hb : M.val.toBilin'.IsOrthoᵢ b := by
    intro i j hij
    change M.val.toBilin' ((v.reindex e') i) ((v.reindex e') j) = 0
    rw [Basis.reindex_apply, Basis.reindex_apply]
    exact (LinearMap.isOrthoᵢ_def.mp hv) (e'.symm i) (e'.symm j) (e'.symm.injective.ne hij)
  let e := Pi.basisFun k (Fin n)
  let A : FunctionsMetaplectic.Construction.GeneralLinear k n := {
    val := e.toMatrix b
    inv := b.toMatrix e
    val_inv := e.toMatrix_mul_toMatrix_flip b
    inv_val := b.toMatrix_mul_toMatrix_flip e }
  let d := fun i => M.val.toBilin' (b i) (b i)
  have hcol (i : Fin n) : A.val.col i = b i := by funext j; rfl
  have hdiag : A.val.transpose * M.val * A.val = diagonal d := by
    ext i j
    rw [SiegelGaussian.Construction.matrix_congruence_entry, hcol, hcol, ← Matrix.toBilin'_apply']
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
      rfl
    · rw [diagonal_apply_ne _ hij]
      exact hb hij
  have hAdet : A.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A.val).mp A.isUnit).ne_zero
  have hMdet : M.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det M.val).mp M.isUnit).ne_zero
  have hprod : ∏ i, d i ≠ 0 := by
    rw [← det_diagonal, ← hdiag, det_mul, det_mul, det_transpose]
    exact mul_ne_zero (mul_ne_zero hAdet hMdet) hAdet
  have hd (i : Fin n) : d i ≠ 0 := (Finset.prod_ne_zero_iff.mp hprod) i (Finset.mem_univ i)
  exact ⟨A, fun i => Units.mk0 (d i) (hd i), hdiag⟩

end

end OAI.RepresentationTheory.Weil.Local.SymmetricCongruenceDiagonal.Construction
