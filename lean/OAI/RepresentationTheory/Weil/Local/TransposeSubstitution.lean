import OAI.RepresentationTheory.Weil.Local.FourierLinearSubstitution

/-! # Transpose Substitution -/

namespace OAI.RepresentationTheory.Weil.Local.TransposeSubstitution.Construction

noncomputable section

/-! Fourier covariance under an arbitrary invertible matrix, with the transpose explicit. -/

open _root_.Matrix _root_.MeasureTheory

def transposeGeneralLinear {k : Type} [Field k] {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n) : FunctionsMetaplectic.Construction.GeneralLinear k n where
  val := A.val.transpose
  inv := A⁻¹.val.transpose
  val_inv := by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]

theorem transposeGeneralLinear_inv {k : Type} [Field k] {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    (transposeGeneralLinear A)⁻¹ = transposeGeneralLinear A⁻¹ := by apply Units.ext; rfl

theorem transposeGeneralLinear_transpose {k : Type} [Field k] {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    transposeGeneralLinear (transposeGeneralLinear A) = A := by
  apply Units.ext
  exact Matrix.transpose_transpose A.val

theorem determinantUnit_transpose
    {k : Type} [NormedField k] [LocallyCompactSpace k] [MeasurableSpace k] [BorelSpace k]
    {n : ℕ} (A : FunctionsMetaplectic.Construction.GeneralLinear k n) : FunctionsMetaplectic.Construction.determinantUnit k (transposeGeneralLinear A) = FunctionsMetaplectic.Construction.determinantUnit k A := by
  apply Units.ext
  exact Matrix.det_transpose A.val

theorem fourierIntegral_transpose_substitution
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (f : FunctionsMetaplectic.Construction.Position k n → ℂ) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) (FunctionsMetaplectic.Construction.substitutionOperator A f) x =
      (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℝ) •
        FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f (A.val.transpose *ᵥ x) := by
  have h := FourierLinearSubstitution.Construction.integral_matrix_inverse μ A (fun y => f y * ψ (-FunctionsMetaplectic.Construction.dot (A.val.transpose *ᵥ x) y))
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    rw [FunctionsMetaplectic.Construction.substitutionOperator_apply]
    congr 2
    have heq : FunctionsMetaplectic.Construction.dot (A.val.transpose *ᵥ x) (A⁻¹.val *ᵥ y) = FunctionsMetaplectic.Construction.dot x y := by
      change (A.val.transpose *ᵥ x) ⬝ᵥ (A⁻¹.val *ᵥ y) = x ⬝ᵥ y
      rw [← Matrix.vecMul_transpose, Matrix.transpose_transpose, Matrix.dotProduct_mulVec,
        Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    exact congrArg Neg.neg heq.symm

theorem quadratic_matrix_congruence {k : Type} [Field k] {n : ℕ}
    (M A : Matrix (Fin n) (Fin n) k) (x : FunctionsMetaplectic.Construction.Position k n) :
    FunctionsMetaplectic.Construction.quadratic (A.transpose * M * A) x = FunctionsMetaplectic.Construction.quadratic M (A *ᵥ x) := by
  rw [QuadraticIntertwiner.Construction.quadratic_eq_dot, QuadraticIntertwiner.Construction.quadratic_eq_dot]
  congr 1
  change x ⬝ᵥ ((A.transpose * M * A) *ᵥ x) = (A *ᵥ x) ⬝ᵥ (M *ᵥ (A *ᵥ x))
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_transpose]

end

end OAI.RepresentationTheory.Weil.Local.TransposeSubstitution.Construction
