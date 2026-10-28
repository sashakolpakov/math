import OAI.NumberTheory.ArithmeticGroups.Lattices.SignedPermutationMatrices
import Mathlib.Topology.Algebra.Group.Units

/-! # Exponential Diagonals -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ExponentialDiagonals.Construction

noncomputable section

/-! Bounded logarithmic diagonals exponentiate into a compact
subset of the positive diagonal matrix units. -/

open scoped _root_.Matrix.Norms.Operator

def exponentialDiagonalMatrixUnit {n : ℕ} (x : Fin n → ℝ) : (Matrix (Fin n) (Fin n) ℝ)ˣ :=
  SignedPermutationMatrices.Construction.nonzeroDiagonalMatrixUnit (fun i => Real.exp (x i)) (fun i => Real.exp_ne_zero (x i))

theorem exponentialDiagonalMatrixUnit_continuous (n : ℕ) :
    Continuous (exponentialDiagonalMatrixUnit (n := n)) := by
  apply Units.isOpenEmbedding_val.isEmbedding.continuous_iff.mpr
  change Continuous (fun x : Fin n → ℝ => Matrix.diagonal (fun i => Real.exp (x i)))
  exact (continuous_pi (fun i => Real.continuous_exp.comp (continuous_apply i))).matrix_diagonal

theorem compact_exponential_diagonals (n : ℕ) (c : ℝ) :
    IsCompact (exponentialDiagonalMatrixUnit ''
      Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) c)) :=
  (isCompact_univ_pi (fun _ => isCompact_Icc)).image (exponentialDiagonalMatrixUnit_continuous n)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ExponentialDiagonals.Construction
