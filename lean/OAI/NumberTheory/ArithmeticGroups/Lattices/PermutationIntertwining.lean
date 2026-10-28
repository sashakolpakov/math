import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationFactorCentralizer
import OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationMatrixUnits
import OAI.NumberTheory.ArithmeticGroups.Lattices.QRGramIntertwining

/-! # Permutation Intertwining -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationIntertwining.Construction

noncomputable section

/-! The bounded core in permutation reduction intertwines the two
common chamber diagonals. Its QR unipotent factor therefore commutes
with the remaining unbounded diagonal. -/

open scoped Classical

theorem permutation_core_diagonal_intertwining {m : ℕ}
    (σ : Equiv.Perm (Fin m)) (U : Matrix (Fin m) (Fin m) ℝ)
    (hU : ∀ i j, ¬(i < j ∧ σ j < σ i) → (U - 1) i j = 0)
    (c y : Fin m → ℝ) (hy : Monotone y) (hyσ : Monotone (y ∘ σ.symm)) :
    (Matrix.diagonal c * U * σ.permMatrix ℝ) * Matrix.diagonal (fun i => y (σ.symm i)) =
      Matrix.diagonal y * (Matrix.diagonal c * U * σ.permMatrix ℝ) := by
  have hu := (PermutationFactorCentralizer.Construction.inversion_supported_matrix_commutes_diagonal σ U hU y hy hyσ).eq
  have hp : σ.permMatrix ℝ * Matrix.diagonal (fun i => y (σ.symm i)) =
      Matrix.diagonal y * σ.permMatrix ℝ := by
    simpa only [Equiv.symm_apply_apply] using SignedPermutationMatrices.Construction.permutation_support_diagonal_intertwining
      (σ.permMatrix ℝ) σ (by intro i j hij; simp [Ne.symm hij]) (fun i => y (σ.symm i))
  have hc : Matrix.diagonal c * Matrix.diagonal y = Matrix.diagonal y * Matrix.diagonal c := by
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  calc
    (Matrix.diagonal c * U * σ.permMatrix ℝ) * Matrix.diagonal (fun i => y (σ.symm i)) =
        Matrix.diagonal c * (U * Matrix.diagonal y) * σ.permMatrix ℝ := by
      simp only [mul_assoc, hp]
    _ = Matrix.diagonal y * (Matrix.diagonal c * U * σ.permMatrix ℝ) := by
      rw [hu, ← mul_assoc (Matrix.diagonal c), hc]
      simp only [mul_assoc]

theorem operatorQR_permutation_core_commutes
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (σ : Equiv.Perm (Fin m))
    (g : (L →L[ℝ] L)ˣ) (U : Matrix (Fin m) (Fin m) ℝ)
    (hU : ∀ i j, ¬(i < j ∧ σ j < σ i) → (U - 1) i j = 0)
    (c y : Fin m → ℝ) (hy : Monotone y) (hyσ : Monotone (y ∘ σ.symm))
    (hg : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val = Matrix.diagonal c * U * σ.permMatrix ℝ) :
    Commute (OperatorQRVal.Construction.operatorQRUnipotentMatrix b g) (Matrix.diagonal (fun i => Real.exp (y (σ.symm i)))) := by
  apply QRGramIntertwining.Construction.operatorQR_unipotent_commutes_of_matrix_intertwining b g y (fun i => y (σ.symm i)) _ Real.exp
  rw [hg]
  exact permutation_core_diagonal_intertwining σ U hU c y hy hyσ

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.PermutationIntertwining.Construction
