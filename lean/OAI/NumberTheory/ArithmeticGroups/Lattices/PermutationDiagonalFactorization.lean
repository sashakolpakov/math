import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ExponentialDiagonals
import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationIntertwining

/-! # Permutation Diagonal Factorization -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationDiagonalFactorization.Construction

noncomputable section

/-! Separating a bounded logarithmic diagonal from a common chamber
diagonal yields the bounded core used in permutation reduction. -/

theorem exponentialDiagonalMatrixUnit_add {n : ℕ} (x y : Fin n → ℝ) :
    Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x + y) = Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit y := by
  apply Units.ext
  change Matrix.diagonal (fun i => Real.exp ((x + y) i)) =
    Matrix.diagonal (fun i => Real.exp (x i)) * Matrix.diagonal (fun i => Real.exp (y i))
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact Real.exp_add _ _

theorem exponentialDiagonalMatrixUnit_permutation {n : ℕ} (σ : Equiv.Perm (Fin n))
    (y : Fin n → ℝ) :
    (PermutationMatrixUnits.Construction.permutationMatrixUnit σ)⁻¹ * Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit y * PermutationMatrixUnits.Construction.permutationMatrixUnit σ =
      Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (y ∘ σ.symm) := by
  apply Units.ext
  exact PermutationMatrixUnits.Construction.permutationMatrixUnit_conjugate_diagonal σ (fun i => Real.exp (y i))

theorem permutation_diagonal_factorization {n : ℕ} (σ : Equiv.Perm (Fin n))
    (u v : (Matrix (Fin n) (Fin n) ℝ)ˣ)
    (hu : ∀ i j, ¬(i < j ∧ σ j < σ i) → (u.val - 1) i j = 0)
    (x y : Fin n → ℝ) (hy : Monotone y) (hyσ : Monotone (y ∘ σ.symm)) :
    Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * (u * v) * PermutationMatrixUnits.Construction.permutationMatrixUnit σ =
      (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x - y) * u * PermutationMatrixUnits.Construction.permutationMatrixUnit σ) *
        Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (y ∘ σ.symm) *
        ((PermutationMatrixUnits.Construction.permutationMatrixUnit σ)⁻¹ * v * PermutationMatrixUnits.Construction.permutationMatrixUnit σ) := by
  have hua : u * Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit y = Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit y * u := by
    apply Units.ext
    exact (QRGramIntertwining.Construction.commute_diagonal_function u.val y
      (PermutationFactorCentralizer.Construction.inversion_supported_matrix_commutes_diagonal σ u.val hu y hy hyσ) Real.exp).eq
  have hx : Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x =
      Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x - y) * Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit y := by
    rw [← exponentialDiagonalMatrixUnit_add, sub_add_cancel]
  rw [← exponentialDiagonalMatrixUnit_permutation, hx]
  calc
    Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x - y) * Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit y * (u * v) *
        PermutationMatrixUnits.Construction.permutationMatrixUnit σ =
      Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x - y) * (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit y * u) * v *
        PermutationMatrixUnits.Construction.permutationMatrixUnit σ := by simp only [mul_assoc]
    _ = _ := by rw [← hua]; group

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationDiagonalFactorization.Construction
