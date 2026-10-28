import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRLogTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal

/-! # QR Compact Triangular Translations -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QRCompactTriangularTranslations.Construction

noncomputable section

/-! Orthogonal left factors and upper unipotent right factors have
explicit actions on the logarithmic and unipotent QR coordinates. -/

theorem operatorQR_orthogonal_unipotent_coordinates
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) (k g n : (L →L[ℝ] L)ˣ)
    (hk : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ)
    (hn : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val)) :
    OperatorQRVal.Construction.operatorQRLogDiagonal b (k * g * n) = OperatorQRVal.Construction.operatorQRLogDiagonal b g ∧
      OperatorQRVal.Construction.operatorQRUnipotentUnit b (k * g * n) =
        OperatorQRVal.Construction.operatorQRUnipotentUnit b g * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis n := by
  constructor
  · rw [OperatorQRLogTranslation.Construction.operatorQRLogDiagonal_right_unipotent b (k * g) n hn,
      OperatorQRLogTranslation.Construction.operatorQRLogDiagonal_left_orthogonal b k g hk]
  · apply Units.ext
    change (OperatorQRVal.Construction.operatorQRUnipotentUnit b (k * g * n)).val =
      (OperatorQRVal.Construction.operatorQRUnipotentUnit b g).val * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val
    rw [OperatorQRVal.Construction.operatorQRUnipotentUnit_val, OperatorQRVal.Construction.operatorQRUnipotentUnit_val,
      (OperatorQRUnipotentTranslation.Construction.operatorQR_right_unipotent b (k * g) n hn).2.2,
      (OperatorQROrthogonalTranslation.Construction.operatorQR_left_orthogonal b k g hk).2.2]

theorem finite_tuple_difference_norm_bound {n : ℕ} (z : Fin n → ℝ) (i j : Fin n) :
    z i - z j ≤ 2 * ‖z‖ := by
  have hi := abs_le.mp (show |z i| ≤ ‖z‖ from norm_le_pi_norm z i)
  have hj := abs_le.mp (show |z j| ≤ ‖z‖ from norm_le_pi_norm z j)
  linarith

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QRCompactTriangularTranslations.Construction
