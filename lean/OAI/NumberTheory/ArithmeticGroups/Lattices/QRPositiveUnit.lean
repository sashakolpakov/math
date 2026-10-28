import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ExponentialDiagonals
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRVal
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRDiagonalTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQROrthogonalTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.OperatorQRUnipotentTranslation
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.TriangularConjugates

/-! # QR Positive Unit -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.QRPositiveUnit.Construction

noncomputable section

section

/-! The positive diagonal QR coordinate as a continuous matrix unit. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

def operatorQRPositiveDiagonalUnit {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) : (Matrix (Fin m) (Fin m) ℝ)ˣ :=
  Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit (OperatorQRVal.Construction.operatorQRLogDiagonal b g)

omit [FiniteDimensional ℝ L] in
theorem operatorQRPositiveDiagonalUnit_val {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g : (L →L[ℝ] L)ˣ) : (operatorQRPositiveDiagonalUnit b g).val = Matrix.diagonal (OperatorQRBasis.Construction.operatorQRDiagonal b g) := by
  change Matrix.diagonal (fun i => Real.exp (Real.log (OperatorQRBasis.Construction.operatorQRDiagonal b g i))) = _
  congr 1
  funext i
  exact Real.exp_log (OperatorQRBasis.Construction.operatorQRDiagonal_pos b g i)

omit [FiniteDimensional ℝ L] in
theorem operatorQRPositiveDiagonalUnit_continuous {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L) :
    Continuous (operatorQRPositiveDiagonalUnit b) :=
  (Compact.ExponentialDiagonals.Construction.exponentialDiagonalMatrixUnit_continuous m).comp (OperatorQRVal.Construction.operatorQRLogDiagonal_continuous b)

theorem operatorQRPositiveDiagonalUnit_right_diagonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g a : (L →L[ℝ] L)ˣ) (d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d) :
    operatorQRPositiveDiagonalUnit b (g * a) =
      operatorQRPositiveDiagonalUnit b g * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis a := by
  apply Units.ext
  change (operatorQRPositiveDiagonalUnit b (g * a)).val =
    (operatorQRPositiveDiagonalUnit b g).val * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val
  rw [operatorQRPositiveDiagonalUnit_val, operatorQRPositiveDiagonalUnit_val, ha,
    (OperatorQRDiagonalTranslation.Construction.operatorQR_right_diagonal b g a d hd ha).2.1, Matrix.diagonal_mul_diagonal]

theorem operatorQRPositiveDiagonalUnit_right_unipotent {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g n : (L →L[ℝ] L)ˣ) (hn : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val)) :
    operatorQRPositiveDiagonalUnit b (g * n) = operatorQRPositiveDiagonalUnit b g := by
  apply Units.ext
  rw [operatorQRPositiveDiagonalUnit_val, operatorQRPositiveDiagonalUnit_val,
    (OperatorQRUnipotentTranslation.Construction.operatorQR_right_unipotent b g n hn).2.1]

theorem operatorQRPositiveDiagonalUnit_left_orthogonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (k g : (L →L[ℝ] L)ˣ) (hk : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    operatorQRPositiveDiagonalUnit b (k * g) = operatorQRPositiveDiagonalUnit b g := by
  apply Units.ext
  rw [operatorQRPositiveDiagonalUnit_val, operatorQRPositiveDiagonalUnit_val,
    (OperatorQROrthogonalTranslation.Construction.operatorQR_left_orthogonal b k g hk).2.1]

end

section

/-! Translation identities for the unipotent QR coordinate in the
matrix unit group. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem operatorQRUnipotentUnit_right_diagonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g a : (L →L[ℝ] L)ˣ) (d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d) :
    OperatorQRVal.Construction.operatorQRUnipotentUnit b (g * a) = (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis a)⁻¹ *
      OperatorQRVal.Construction.operatorQRUnipotentUnit b g * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis a := by
  apply Units.ext
  change (OperatorQRVal.Construction.operatorQRUnipotentUnit b (g * a)).val =
    ((ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis a)⁻¹).val * (OperatorQRVal.Construction.operatorQRUnipotentUnit b g).val *
      ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val
  rw [OperatorQRVal.Construction.operatorQRUnipotentUnit_val, OperatorQRVal.Construction.operatorQRUnipotentUnit_val,
    Compact.TriangularConjugates.Construction.diagonal_matrix_unit_inverse (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis a) d (fun i => ne_of_gt (hd i)) ha,
    ha, (OperatorQRDiagonalTranslation.Construction.operatorQR_right_diagonal b g a d hd ha).2.2]

theorem operatorQRUnipotentUnit_right_unipotent {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (g n : (L →L[ℝ] L)ˣ) (hn : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val)) :
    OperatorQRVal.Construction.operatorQRUnipotentUnit b (g * n) = OperatorQRVal.Construction.operatorQRUnipotentUnit b g * ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis n := by
  apply Units.ext
  change (OperatorQRVal.Construction.operatorQRUnipotentUnit b (g * n)).val =
    (OperatorQRVal.Construction.operatorQRUnipotentUnit b g).val * ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis n.val
  rw [OperatorQRVal.Construction.operatorQRUnipotentUnit_val, OperatorQRVal.Construction.operatorQRUnipotentUnit_val, (OperatorQRUnipotentTranslation.Construction.operatorQR_right_unipotent b g n hn).2.2]

theorem operatorQRUnipotentUnit_left_orthogonal {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (k g : (L →L[ℝ] L)ˣ) (hk : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis k.val ∈ Matrix.orthogonalGroup (Fin m) ℝ) :
    OperatorQRVal.Construction.operatorQRUnipotentUnit b (k * g) = OperatorQRVal.Construction.operatorQRUnipotentUnit b g := by
  apply Units.ext
  rw [OperatorQRVal.Construction.operatorQRUnipotentUnit_val, OperatorQRVal.Construction.operatorQRUnipotentUnit_val, (OperatorQROrthogonalTranslation.Construction.operatorQR_left_orthogonal b k g hk).2.2]

end

/-! Cancellation of the unbounded diagonal in the normalized mixed
QR unipotent product, with a compactness consequence. -/

variable {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

theorem operatorQR_normalized_mixed_product {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (q a v : (L →L[ℝ] L)ˣ) (d : Fin m → ℝ) (hd : ∀ i, 0 < d i)
    (ha : ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d)
    (hv : UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis v.val)) :
    operatorQRPositiveDiagonalUnit b (q * a * v) * OperatorQRVal.Construction.operatorQRUnipotentUnit b (q * a * v) *
      (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis v)⁻¹ * (operatorQRPositiveDiagonalUnit b (q * a * v))⁻¹ =
        operatorQRPositiveDiagonalUnit b q * OperatorQRVal.Construction.operatorQRUnipotentUnit b q * (operatorQRPositiveDiagonalUnit b q)⁻¹ := by
  rw [operatorQRPositiveDiagonalUnit_right_unipotent b (q * a) v hv,
    operatorQRUnipotentUnit_right_unipotent b (q * a) v hv,
    operatorQRPositiveDiagonalUnit_right_diagonal b q a d hd ha,
    operatorQRUnipotentUnit_right_diagonal b q a d hd ha]
  group

theorem compact_operatorQR_normalized_mixed_products {m : ℕ} (b : OrthonormalBasis (Fin m) ℝ L)
    (Q : Set (L →L[ℝ] L)ˣ) (hQ : IsCompact Q) :
    ∃ D : Set (Matrix (Fin m) (Fin m) ℝ)ˣ, IsCompact D ∧
      ∀ q ∈ Q, ∀ a v : (L →L[ℝ] L)ˣ, ∀ d : Fin m → ℝ,
        (∀ i, 0 < d i) → ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis a.val = Matrix.diagonal d →
        UpperUnitriangularMatrices.Construction.IsUpperUnitriangular (ContinuousOperatorExponentialDeterminant.Construction.continuousEndMatrix b.toBasis v.val) →
        operatorQRPositiveDiagonalUnit b (q * a * v) * OperatorQRVal.Construction.operatorQRUnipotentUnit b (q * a * v) *
          (ContinuousEndMatrixEquiv.Construction.continuousEndMatrixUnitsEquiv b.toBasis v)⁻¹ * (operatorQRPositiveDiagonalUnit b (q * a * v))⁻¹ ∈ D := by
  let f := fun q => operatorQRPositiveDiagonalUnit b q * OperatorQRVal.Construction.operatorQRUnipotentUnit b q *
    (operatorQRPositiveDiagonalUnit b q)⁻¹
  have hf : Continuous f := ((operatorQRPositiveDiagonalUnit_continuous b).mul
    (OperatorQRVal.Construction.operatorQRUnipotentUnit_continuous b)).mul (operatorQRPositiveDiagonalUnit_continuous b).inv
  refine ⟨f '' Q, hQ.image hf, fun q hq a v d hd ha hv => ?_⟩
  rw [operatorQR_normalized_mixed_product b q a v d hd ha hv]
  exact ⟨q, hq, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.QRPositiveUnit.Construction
