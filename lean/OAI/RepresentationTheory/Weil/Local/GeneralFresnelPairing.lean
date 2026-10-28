import OAI.RepresentationTheory.Weil.Local.QuadraticDiagonalData
import OAI.RepresentationTheory.Weil.Local.FresnelChangeCoordinates

/-! # General Fresnel Pairing -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralFresnelPairing.Construction

noncomputable section

/-! The actual nonarchimedean Fresnel pairing for a general nonsingular symmetric form. -/

open _root_.Matrix _root_.MeasureTheory

theorem integral_fourier_transpose_substitution_phase
    {k : Type} [NormedField k] [LocallyCompactSpace k]
    [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
    (ψ : AddChar k ℂ) (μ : Measure k) [μ.IsAddHaarMeasure]
    (A : FunctionsMetaplectic.Construction.GeneralLinear k n) (f P Q : FunctionsMetaplectic.Construction.Position k n → ℂ)
    (hPQ : ∀ x, P (A⁻¹.val *ᵥ x) = Q x) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ))
      (FunctionsMetaplectic.Construction.substitutionOperator (TransposeSubstitution.Construction.transposeGeneralLinear A) f) x * P x
      ∂Measure.pi (fun _ : Fin n => μ)) =
      ∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f x * Q x
        ∂Measure.pi (fun _ : Fin n => μ) := by
  let d := FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A)
  let g := fun x => FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f (A.val *ᵥ x) * P x
  calc
    _ = d • ∫ x, g x ∂Measure.pi (fun _ : Fin n => μ) := by
      rw [← integral_smul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [TransposeSubstitution.Construction.fourierIntegral_transpose_substitution, TransposeSubstitution.Construction.determinantUnit_transpose]
        change ((FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℝ) •
          FunctionsMetaplectic.Construction.fourierIntegral ψ (Measure.pi (fun _ : Fin n => μ)) f (A.val.transpose.transpose *ᵥ x)) * P x = _
        rw [Matrix.transpose_transpose]
        dsimp only [g, d]
        simp only [Complex.real_smul]
        ring
    _ = ∫ x, g (A⁻¹.val *ᵥ x) ∂Measure.pi (fun _ : Fin n => μ) :=
      (FourierLinearSubstitution.Construction.integral_matrix_inverse μ A g).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only [g]
        rw [hPQ, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]

theorem nonarchimedean_general_fresnel_pairing_of_diagonalization
    {k : Type} [NormedField k] [LocallyCompactSpace k] [NonarchimedeanAddGroup k] [CharZero k]
    [MeasurableSpace k] [BorelSpace k]
    (hnd : ¬ DiscreteTopology k) {n : ℕ}
    (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1) (hc : Continuous (fun t => ψ t))
    (hn : ∃ t : k, ψ t ≠ 1) (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (hdiag : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val))
    (f : FunctionsMetaplectic.Construction.schwartzBruhat k n) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x * ψ (FunctionsMetaplectic.Construction.quadratic M.val x)
      ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ) =
      ((FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) * DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a) *
        ∫ x, f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ := by
  let : SecondCountableTopology k := FunctionsMetaplectic.Construction.localField_secondCountable k hnd
  let μ := FunctionsMetaplectic.Construction.selfDualMeasure k ψ
  let : μ.IsAddHaarMeasure := NonarchimedeanHaar.Construction.nonarchimedean_selfDualMeasure_isAddHaarMeasure hnd ψ hu hc hn
  have hp := DiagonalQuadratic.Construction.nonarchimedean_diagonal_fresnel_pairing hnd ψ hu hc hn a
    (LinearSubstitution.Construction.testSubstitution (TransposeSubstitution.Construction.transposeGeneralLinear A) f)
  have hleft := integral_fourier_transpose_substitution_phase ψ μ A f.val
    (fun x => ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) x)) (fun x => ψ (FunctionsMetaplectic.Construction.quadratic M.val x))
    (fun x => congrArg ψ (QuadraticDiagonalData.Construction.quadratic_diagonal_inverse_coordinates M A a hdiag x))
  have hright := FresnelChangeCoordinates.Construction.integral_substitution_mul_phase μ (TransposeSubstitution.Construction.transposeGeneralLinear A) f.val
    (fun x => ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x)) (fun x => ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val x))
    (fun x => congrArg ψ (congrArg Neg.neg (QuadraticDiagonalData.Construction.quadratic_inverse_diagonal_coordinates M A a hdiag x)))
  change (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ)
      (FunctionsMetaplectic.Construction.substitutionOperator (TransposeSubstitution.Construction.transposeGeneralLinear A) f.val) x *
        ψ (FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val) x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ) =
    DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a *
      ∫ x, FunctionsMetaplectic.Construction.substitutionOperator (TransposeSubstitution.Construction.transposeGeneralLinear A) f.val x *
        ψ (-FunctionsMetaplectic.Construction.quadratic (diagonal fun i => (a i).val⁻¹) x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ at hp
  dsimp only [μ, FunctionsMetaplectic.Construction.positionMeasure] at hp hleft hright ⊢
  rw [hleft, hright, TransposeSubstitution.Construction.determinantUnit_transpose, Complex.real_smul] at hp
  exact hp.trans (by ring)

end

end OAI.RepresentationTheory.Weil.Local.GeneralFresnelPairing.Construction
