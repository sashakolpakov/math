import OAI.NumberTheory.ArithmeticGroups.Lattices.QRCompactLogBounds
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRLogTranslation

/-! # QR Chamber Bound -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QRChamberBound.Construction

noncomputable section

/-! A compact factor followed by a diagonal in the closed negative
ambient chamber has a uniformly bounded QR chamber coordinate. -/

theorem compact_factor_right_chamber_qr_bound
    {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]
    {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (Q : Set (L →L[ℝ] L)ˣ) (hQ : IsCompact Q) :
    ∃ s : ℝ, 0 ≤ s ∧ ∀ q ∈ Q, ∀ k a : (L →L[ℝ] L)ˣ, ∀ y : Fin m → ℝ,
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ →
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal (fun i => Real.exp (y i)) →
      Monotone y → ∀ i j, i ≤ j →
        OperatorQRVal.Construction.operatorQRLogDiagonal b (k * q * a) i - OperatorQRVal.Construction.operatorQRLogDiagonal b (k * q * a) j ≤ s := by
  obtain ⟨c, hc, hb⟩ := QRCompactLogBounds.Construction.compact_operatorQR_log_bound b Q hQ
  refine ⟨2 * c, mul_nonneg (by norm_num) hc, fun q hq k a y hk ha hy i j hij => ?_⟩
  have hi := abs_le.mp (hb q hq i)
  have hj := abs_le.mp (hb q hq j)
  have hiy := OperatorQRLogTranslation.Construction.operatorQRLogDiagonal_right_diagonal b q a _ (fun i => Real.exp_pos _) ha i
  have hjy := OperatorQRLogTranslation.Construction.operatorQRLogDiagonal_right_diagonal b q a _ (fun i => Real.exp_pos _) ha j
  rw [Real.log_exp] at hiy hjy
  have hmono := hy hij
  rw [mul_assoc, OperatorQRLogTranslation.Construction.operatorQRLogDiagonal_left_orthogonal b k (q * a) hk]
  linarith

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.QRChamberBound.Construction
