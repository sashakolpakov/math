import OAI.RepresentationTheory.Weil.Local.FourierNormalForm
import OAI.RepresentationTheory.Weil.Local.TransposeSubstitution

/-! # Symmetric Matrix Operations -/

namespace OAI.RepresentationTheory.Weil.Local.SymmetricMatrixOperations.Construction

noncomputable section

/-! Symmetric matrix operations for Fourier normal form products. -/

open _root_.Matrix

variable {k : Type} [Field k] {n : ℕ}

def symmetricAdd (P Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) : FunctionsMetaplectic.Construction.SymmetricMatrix k n :=
  ⟨P.val + Q.val, P.property.add Q.property⟩

def symmetricCongruence (A : Matrix (Fin n) (Fin n) k) (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    FunctionsMetaplectic.Construction.SymmetricMatrix k n :=
  ⟨A.transpose * P.val * A, by
    change (A.transpose * P.val * A).transpose = A.transpose * P.val * A
    rw [transpose_mul, transpose_mul, transpose_transpose, P.property.eq, Matrix.mul_assoc]⟩

def symmetricNegativeInverse (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) :
    FunctionsMetaplectic.Construction.SymmetricMatrix k n :=
  ⟨-M⁻¹.val, by simpa only [Matrix.coe_units_inv] using hM.inv.neg⟩

theorem quadraticSymplectic_add (P Q : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    Generators.Construction.quadraticSymplectic P * Generators.Construction.quadraticSymplectic Q = Generators.Construction.quadraticSymplectic (symmetricAdd P Q) := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 0 P.val 1 * Matrix.fromBlocks 1 0 Q.val 1 =
    Matrix.fromBlocks 1 0 (P.val + Q.val) 1
  simp [Matrix.fromBlocks_multiply]

theorem quadraticSymplectic_levi_congruence (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    Generators.Construction.quadraticSymplectic P * Generators.Construction.leviSymplectic A =
      Generators.Construction.leviSymplectic A * Generators.Construction.quadraticSymplectic (symmetricCongruence A.val P) := by
  apply Subtype.ext
  change Matrix.fromBlocks 1 0 P.val 1 * Matrix.fromBlocks A.val 0 0 A⁻¹.val.transpose =
    Matrix.fromBlocks A.val 0 0 A⁻¹.val.transpose * Matrix.fromBlocks 1 0 (A.val.transpose * P.val * A.val) 1
  have hc : A⁻¹.val.transpose * A.val.transpose = 1 := by
    rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one]
  simp only [Matrix.fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero]
  rw [← Matrix.mul_assoc A⁻¹.val.transpose, ← Matrix.mul_assoc A⁻¹.val.transpose, hc, one_mul]

theorem levi_quadraticSymplectic_congruence (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (P : FunctionsMetaplectic.Construction.SymmetricMatrix k n) :
    Generators.Construction.leviSymplectic A * Generators.Construction.quadraticSymplectic P =
      Generators.Construction.quadraticSymplectic (symmetricCongruence A⁻¹.val P) * Generators.Construction.leviSymplectic A := by
  apply Subtype.ext
  change Matrix.fromBlocks A.val 0 0 A⁻¹.val.transpose * Matrix.fromBlocks 1 0 P.val 1 =
    Matrix.fromBlocks 1 0 (A⁻¹.val.transpose * P.val * A⁻¹.val) 1 * Matrix.fromBlocks A.val 0 0 A⁻¹.val.transpose
  simp only [Matrix.fromBlocks_multiply, one_mul, mul_one, zero_mul, mul_zero, zero_add, add_zero]
  rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]

theorem weyl_levi_transpose (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    Generators.Construction.weylSymplectic k n * Generators.Construction.leviSymplectic A =
      Generators.Construction.leviSymplectic (TransposeSubstitution.Construction.transposeGeneralLinear A)⁻¹ * Generators.Construction.weylSymplectic k n := by
  apply Subtype.ext
  change Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks A.val 0 0 A⁻¹.val.transpose =
    Matrix.fromBlocks A⁻¹.val.transpose 0 0 (A.val.transpose).transpose * Matrix.fromBlocks 0 1 (-1) 0
  simp [Matrix.fromBlocks_multiply]

theorem weyl_quadratic_weyl (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) :
    Generators.Construction.weylSymplectic k n * Generators.Construction.quadraticSymplectic ⟨M.val, hM⟩ * Generators.Construction.weylSymplectic k n =
      FourierNormalForm.Construction.fourierNormalForm (symmetricNegativeInverse M hM) M (symmetricNegativeInverse M hM) := by
  apply Subtype.ext
  rw [FourierNormalForm.Construction.fourierNormalForm_matrix]
  change Matrix.fromBlocks 0 1 (-1) 0 * Matrix.fromBlocks 1 0 M.val 1 * Matrix.fromBlocks 0 1 (-1) 0 =
    Matrix.fromBlocks (M.val * (-M⁻¹.val)) M.val
      ((-M⁻¹.val) * M.val * (-M⁻¹.val) - M⁻¹.val.transpose) ((-M⁻¹.val) * M.val)
  simp [Matrix.fromBlocks_multiply, hM.inv.eq]

end

end OAI.RepresentationTheory.Weil.Local.SymmetricMatrixOperations.Construction
