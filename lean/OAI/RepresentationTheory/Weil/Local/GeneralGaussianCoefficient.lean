import OAI.RepresentationTheory.Weil.Local.GeneralFresnelPairing
import OAI.RepresentationTheory.Weil.Local.GaussianDeterminantSquare

/-! # General Gaussian Coefficient -/

namespace OAI.RepresentationTheory.Weil.Local.GeneralGaussianCoefficient.Construction

noncomputable section

/-! A general Fresnel coefficient with a checked square, using the actual normalized scalar Gaussian index. -/

open _root_.Matrix _root_.MeasureTheory

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

theorem generalGaussianCoefficient_square {n : ℕ} (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) :
    ((FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) * DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a) ^ 2 =
      (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) *
        (GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k M)).val) /
          (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k M) : ℂ) := by
  have hA0 : (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FunctionsMetaplectic.Construction.localModulus_pos k _).ne'
  have hM0 : (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k M) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (FunctionsMetaplectic.Construction.localModulus_pos k _).ne'
  rw [mul_pow, GaussianDeterminantSquare.Construction.diagonalGaussianCoefficient_square hnd ψ hu hc hn hns a,
    GaussianDeterminantSquare.Construction.gaussianSquareCharacter_congruence hnd ψ hu hc hn hns M A a h,
    GaussianDeterminantSquare.Construction.localModulus_congruence M A a h, Complex.ofReal_mul, Complex.ofReal_pow]
  field_simp

theorem exists_nonarchimedean_general_fresnel_coefficient {n : ℕ}
    (M : FunctionsMetaplectic.Construction.GeneralLinear k n) (hM : M.val.IsSymm) :
    ∃ c : ℂ,
      c ^ 2 = (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) *
        (GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k M)).val) /
          (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k M) : ℂ) ∧
      ∀ f : FunctionsMetaplectic.Construction.schwartzBruhat k n,
        (∫ x, FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure k n ψ) f.val x * ψ (FunctionsMetaplectic.Construction.quadratic M.val x)
          ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ) =
          c * ∫ x, f.val x * ψ (-FunctionsMetaplectic.Construction.quadratic M⁻¹.val x) ∂ FunctionsMetaplectic.Construction.positionMeasure k n ψ := by
  obtain ⟨A, a, ha⟩ := SymmetricCongruenceDiagonal.Construction.symmetric_generalLinear_congruence_diagonal M hM
  exact ⟨(FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) : ℂ) * DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a,
    generalGaussianCoefficient_square hnd ψ hu hc hn hns M A a ha,
    GeneralFresnelPairing.Construction.nonarchimedean_general_fresnel_pairing_of_diagonalization hnd ψ hu hc hn M A a ha⟩

end

end OAI.RepresentationTheory.Weil.Local.GeneralGaussianCoefficient.Construction
