import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation

/-! # Operator QR Unipotent Translation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRUnipotentTranslation.Construction

noncomputable section

/-! Right upper unipotent translation leaves the compact and diagonal
QR factors unchanged and multiplies the unipotent factor. -/

theorem operatorQR_right_unipotent
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (g n : (L →L[ℝ] L)ˣ)
    (hn : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val)) :
    OperatorQRVal.Construction.operatorQRCompactMatrix b (g * n) = OperatorQRVal.Construction.operatorQRCompactMatrix b g ∧
      OperatorQRBasis.Construction.operatorQRDiagonal b (g * n) = OperatorQRBasis.Construction.operatorQRDiagonal b g ∧
      OperatorQRVal.Construction.operatorQRUnipotentMatrix b (g * n) =
        OperatorQRVal.Construction.operatorQRUnipotentMatrix b g * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val := by
  apply OperatorQRDiagonalTranslation.Construction.operatorQR_kan_unique b (g * n) _ _ _ (OperatorQRVal.Construction.operatorQRCompactMatrix_orthogonal b g)
    (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g) ((OperatorQRVal.Construction.operatorQRUnipotentMatrix_unitriangular b g).mul hn)
  change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (g.val * n.val) = _
  rw [map_mul, OperatorQRVal.Construction.operatorQR_kan_factorization b g]
  simp only [mul_assoc]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRUnipotentTranslation.Construction
