import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal
import OAI.NumberTheory.ArithmeticGroups.Lattices.MatrixKANUniqueness
import OAI.NumberTheory.ArithmeticGroups.Lattices.UpperDiagonalConjugation

/-! # Operator QR Diagonal Translation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation.Construction

noncomputable section

section

/-! The Gram--Schmidt QR factors agree with every positive-diagonal
KAN factorization of the same operator. -/

theorem operatorQR_kan_unique
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g : (L →L[ℝ] L)ˣ)
    (K U : Matrix (Fin m) (Fin m) ℝ) (a : Fin m → ℝ)
    (hK : K ∈ Matrix.orthogonalGroup (Fin m) ℝ) (ha : ∀ i, 0 < a i)
    (hU : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular U) (he : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis g.val = K * Matrix.diagonal a * U) :
    OperatorQRVal.Construction.operatorQRCompactMatrix b g = K ∧ OperatorQRBasis.Construction.operatorQRDiagonal b g = a ∧ OperatorQRVal.Construction.operatorQRUnipotentMatrix b g = U :=
  MatrixKANUniqueness.Construction.matrix_kan_factorization_unique _ K _ U _ a (OperatorQRVal.Construction.operatorQRCompactMatrix_orthogonal b g) hK
    (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g) ha (OperatorQRVal.Construction.operatorQRUnipotentMatrix_unitriangular b g) hU
    ((OperatorQRVal.Construction.operatorQR_kan_factorization b g).symm.trans he)

end

/-! Right multiplication by a positive diagonal scales the QR
diagonal and conjugates its unipotent factor. -/

open scoped Classical

theorem operatorQR_right_diagonal
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g a : (L →L[ℝ] L)ˣ)
    (d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d) :
    OperatorQRVal.Construction.operatorQRCompactMatrix b (g * a) = OperatorQRVal.Construction.operatorQRCompactMatrix b g ∧
      OperatorQRBasis.Construction.operatorQRDiagonal b (g * a) = (fun i => OperatorQRBasis.Construction.operatorQRDiagonal b g i * d i) ∧
      OperatorQRVal.Construction.operatorQRUnipotentMatrix b (g * a) = Matrix.diagonal (fun i => (d i)⁻¹) *
        OperatorQRVal.Construction.operatorQRUnipotentMatrix b g * Matrix.diagonal d := by
  let D := Matrix.diagonal (fun i => OperatorQRBasis.Construction.operatorQRDiagonal b g i * d i)
  have hDD : D * Matrix.diagonal (fun i => (d i)⁻¹) = Matrix.diagonal (OperatorQRBasis.Construction.operatorQRDiagonal b g) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt (hd i)), mul_one]
  have hU : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (Matrix.diagonal (fun i => (d i)⁻¹) *
      OperatorQRVal.Construction.operatorQRUnipotentMatrix b g * Matrix.diagonal d) := by
    simpa only [inv_inv] using (OperatorQRVal.Construction.operatorQRUnipotentMatrix_unitriangular b g).diagonal_conjugation
      (fun i => (d i)⁻¹) (fun i => inv_ne_zero (ne_of_gt (hd i)))
  apply operatorQR_kan_unique b (g * a) (OperatorQRVal.Construction.operatorQRCompactMatrix b g) _ _
    (OperatorQRVal.Construction.operatorQRCompactMatrix_orthogonal b g)
    (fun i => mul_pos (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g i) (hd i)) hU
  change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (g.val * a.val) = _
  rw [map_mul, ha, OperatorQRVal.Construction.operatorQR_kan_factorization b g]
  change OperatorQRVal.Construction.operatorQRCompactMatrix b g * Matrix.diagonal (OperatorQRBasis.Construction.operatorQRDiagonal b g) *
    OperatorQRVal.Construction.operatorQRUnipotentMatrix b g * Matrix.diagonal d =
    OperatorQRVal.Construction.operatorQRCompactMatrix b g * D *
      (Matrix.diagonal (fun i => (d i)⁻¹) * OperatorQRVal.Construction.operatorQRUnipotentMatrix b g * Matrix.diagonal d)
  rw [← hDD]
  simp only [mul_assoc]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation.Construction
