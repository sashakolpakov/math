import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixBruhatDecomposition
import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationDiagonalFactorization
import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperDiagonalConjugation

/-! # Bruhat Siegel Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.BruhatSiegelCoordinates.Construction

noncomputable section

/-! A fixed ambient translate is reduced to a permutation by a
fixed logarithmic shift and a continuous change of upper unipotent coordinates. -/

open scoped Classical

theorem matrix_bruhat_siegel_coordinates {m : ℕ} (M : (Matrix (Fin m) (Fin m) ℝ)ˣ) :
    ∃ S V : (Matrix (Fin m) (Fin m) ℝ)ˣ, ∃ z : Fin m → ℝ, ∃ σ : Equiv.Perm (Fin m),
      ∃ Φ : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m → UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m,
        S.val ∈ Matrix.orthogonalGroup (Fin m) ℝ ∧ UpperUnitriangularMatrices.Construction.IsUpperUnitriangular V.val ∧ Continuous Φ ∧
        ∀ (x : Fin m → ℝ) (n : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m),
          Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * M =
            S * Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (x + z) * (Φ n).val * PermutationMatrixUnits.Construction.permutationMatrixUnit σ * V := by
  obtain ⟨U, V, d, σ, hU, hV, hd, hMval⟩ := MatrixBruhatDecomposition.Construction.exists_matrix_bruhat_decomposition M
  let D := SignedPermutationMatrices.Construction.nonzeroDiagonalMatrixUnit d hd
  let z := fun i => Real.log |d i|
  let A := Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit z
  let S := D * A⁻¹
  let s := fun i => d i / |d i|
  have hSval : S.val = Matrix.diagonal s := by
    change Matrix.diagonal d * Matrix.diagonal (fun i => (Real.exp (z i))⁻¹) = _
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [z, Real.exp_log (abs_pos.mpr (hd i)), s, div_eq_mul_inv]
  have hs : ∀ i, s i * s i = 1 := by
    intro i
    dsimp only [s]
    rw [div_mul_div_comm, abs_mul_abs_self, div_self (mul_ne_zero (hd i) (hd i))]
  have hS : S.val ∈ Matrix.orthogonalGroup (Fin m) ℝ := by
    rw [hSval]
    simpa only [Matrix.permMatrix_refl, mul_one] using!
      SignedPermutationMatrices.Construction.signed_permutation_orthogonal (Equiv.refl _) s hs
  let Φ : UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m → UpperUnitriangularGroup.Construction.upperUnitriangularMatrixGroup m := fun n =>
    ⟨D⁻¹ * (n.val * U) * D, by
      change UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (Matrix.diagonal (fun i => (d i)⁻¹) *
        (n.val.val * U.val) * Matrix.diagonal d)
      simpa only [inv_inv] using (n.property.mul hU).diagonal_conjugation (fun i => (d i)⁻¹)
        (fun i => inv_ne_zero (hd i))⟩
  have hΦ : Continuous Φ :=
    ((continuous_const.mul (continuous_subtype_val.mul continuous_const)).mul continuous_const).subtype_mk _
  have hM : M = U * D * PermutationMatrixUnits.Construction.permutationMatrixUnit σ * V := by
    apply Units.ext
    exact hMval
  refine ⟨S, V, z, σ, Φ, hS, hV, hΦ, fun x n => ?_⟩
  have hcomm : S * Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x = Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * S := by
    apply Units.ext
    change S.val * Matrix.diagonal (fun i => Real.exp (x i)) =
      Matrix.diagonal (fun i => Real.exp (x i)) * S.val
    rw [hSval, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  rw [hM, PermutationDiagonalFactorization.Construction.exponentialDiagonalMatrixUnit_add]
  change Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * n.val * (U * D * PermutationMatrixUnits.Construction.permutationMatrixUnit σ * V) =
    S * (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * A) * (D⁻¹ * (n.val * U) * D) * PermutationMatrixUnits.Construction.permutationMatrixUnit σ * V
  symm
  calc
    S * (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * A) * (D⁻¹ * (n.val * U) * D) * PermutationMatrixUnits.Construction.permutationMatrixUnit σ * V =
      Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit x * (S * A) * (D⁻¹ * (n.val * U) * D) * PermutationMatrixUnits.Construction.permutationMatrixUnit σ * V := by
        rw [← mul_assoc S, hcomm]
        simp only [mul_assoc]
    _ = _ := by dsimp only [S]; group

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.BruhatSiegelCoordinates.Construction
