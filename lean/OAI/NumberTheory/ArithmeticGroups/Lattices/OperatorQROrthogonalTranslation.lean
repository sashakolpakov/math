import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation

/-! # Operator QR Orthogonal Translation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQROrthogonalTranslation.Construction

noncomputable section

/-! Left orthogonal translation preserves the diagonal and unipotent
QR coordinates. -/

theorem operatorQR_left_orthogonal
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (k g : (L →L[ℝ] L)ˣ)
    (hk : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    OperatorQRVal.Construction.operatorQRCompactMatrix b (k * g) = ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val * OperatorQRVal.Construction.operatorQRCompactMatrix b g ∧
      OperatorQRBasis.Construction.operatorQRDiagonal b (k * g) = OperatorQRBasis.Construction.operatorQRDiagonal b g ∧
      OperatorQRVal.Construction.operatorQRUnipotentMatrix b (k * g) = OperatorQRVal.Construction.operatorQRUnipotentMatrix b g := by
  apply OperatorQRDiagonalTranslation.Construction.operatorQR_kan_unique b (k * g) _ _ _
    ((Matrix.orthogonalGroup (Fin m) ℝ).mul_mem hk (OperatorQRVal.Construction.operatorQRCompactMatrix_orthogonal b g))
    (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g) (OperatorQRVal.Construction.operatorQRUnipotentMatrix_unitriangular b g)
  change ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis (k.val * g.val) = _
  rw [map_mul, OperatorQRVal.Construction.operatorQR_kan_factorization b g]
  simp only [mul_assoc]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQROrthogonalTranslation.Construction
