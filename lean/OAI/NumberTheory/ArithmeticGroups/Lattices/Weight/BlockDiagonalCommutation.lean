import OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.BlockProjection
import Mathlib.Basic.Real.Basic

/-! # Block Diagonal Commutation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.BlockDiagonalCommutation.Construction

noncomputable section

/-! Equal-weight blocks commute with every diagonal matrix whose
entries are constant on those weight blocks. -/

open scoped Classical

theorem weightBlockProjection_commutes_diagonal
    {n : ℕ} (w a : Fin n → ℝ) (ha : ∀ i j, w i = w j → a i = a j)
    (M : Matrix (Fin n) (Fin n) ℝ) :
    Commute (BlockProjection.Construction.weightBlockProjection w M) (Matrix.diagonal a) := by
  change BlockProjection.Construction.weightBlockProjection w M * Matrix.diagonal a = Matrix.diagonal a * BlockProjection.Construction.weightBlockProjection w M
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, BlockProjection.Construction.weightBlockProjection_apply]
  by_cases hij : w i = w j
  · rw [ite_eq_left hij, ha i j hij, mul_comm]
  · rw [ite_eq_right hij, zero_mul, mul_zero]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Weight.BlockDiagonalCommutation.Construction
