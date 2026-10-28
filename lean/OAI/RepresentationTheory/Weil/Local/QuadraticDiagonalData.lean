import OAI.RepresentationTheory.Weil.Local.SymmetricCongruenceDiagonal
import OAI.RepresentationTheory.Weil.Local.TransposeSubstitution

/-! # Quadratic Diagonal Data -/

namespace OAI.RepresentationTheory.Weil.Local.QuadraticDiagonalData.Construction

noncomputable section

/-! Quadratic identities and inverse matrices for a chosen congruence diagonalization. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

theorem congruence_diagonal_inverse (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) :
    M⁻¹.val = A.val * diagonal (fun i => (a i).val⁻¹) * A.val.transpose := by
  have he : TransposeSubstitution.Construction.transposeGeneralLinear A * M * A = DiagonalAlgebra.Construction.diagonalGeneralLinear a := Units.ext h
  have hi : M⁻¹ = A * (DiagonalAlgebra.Construction.diagonalGeneralLinear a)⁻¹ * TransposeSubstitution.Construction.transposeGeneralLinear A := by
    rw [← he]
    group
  have hv := congrArg Units.val hi
  rw [DiagonalAlgebra.Construction.diagonalGeneralLinear_inv] at hv
  simpa only [Units.val_mul, DiagonalAlgebra.Construction.diagonalGeneralLinear, TransposeSubstitution.Construction.transposeGeneralLinear, Units.val_inv_eq_inv_val] using hv

theorem quadratic_diagonal_inverse_coordinates (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) (A⁻¹.val *ᵥ x) = FunctionsMetaplectic.Construction.quadratic M.val x := by
  rw [← h, TransposeSubstitution.Construction.quadratic_matrix_congruence, Matrix.mulVec_mulVec, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, one_mulVec]

theorem quadratic_inverse_diagonal_coordinates (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) (A.val.transpose *ᵥ x) = FunctionsMetaplectic.Construction.quadratic M⁻¹.val x := by
  rw [congruence_diagonal_inverse M A a h, ← TransposeSubstitution.Construction.quadratic_matrix_congruence, Matrix.transpose_transpose]

end

end OAI.RepresentationTheory.Weil.Local.QuadraticDiagonalData.Construction
