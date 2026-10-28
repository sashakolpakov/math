import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQROrthogonalTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRUnipotentTranslation

/-! # Operator QR Log Translation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRLogTranslation.Construction

noncomputable section

/-! Additive translation laws for logarithmic QR diagonals. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem operatorQRLogDiagonal_right_diagonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g a : (L →L[ℝ] L)ˣ) (d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d) (i : Fin m) :
    OperatorQRVal.Construction.operatorQRLogDiagonal b (g * a) i = OperatorQRVal.Construction.operatorQRLogDiagonal b g i + Real.log (d i) := by
  unfold OperatorQRVal.Construction.operatorQRLogDiagonal
  rw [congrFun (OperatorQRDiagonalTranslation.Construction.operatorQR_right_diagonal b g a d hd ha).2.1 i]
  exact Real.log_mul (ne_of_gt (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g i)) (ne_of_gt (hd i))

theorem operatorQRLogDiagonal_left_orthogonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (k g : (L →L[ℝ] L)ˣ)
    (hk : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    OperatorQRVal.Construction.operatorQRLogDiagonal b (k * g) = OperatorQRVal.Construction.operatorQRLogDiagonal b g := by
  funext i
  unfold OperatorQRVal.Construction.operatorQRLogDiagonal
  rw [(OperatorQROrthogonalTranslation.Construction.operatorQR_left_orthogonal b k g hk).2.1]

theorem operatorQRLogDiagonal_right_unipotent {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g n : (L →L[ℝ] L)ˣ) (hn : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val)) :
    OperatorQRVal.Construction.operatorQRLogDiagonal b (g * n) = OperatorQRVal.Construction.operatorQRLogDiagonal b g := by
  funext i
  unfold OperatorQRVal.Construction.operatorQRLogDiagonal
  rw [(OperatorQRUnipotentTranslation.Construction.operatorQR_right_unipotent b g n hn).2.1]

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRLogTranslation.Construction
