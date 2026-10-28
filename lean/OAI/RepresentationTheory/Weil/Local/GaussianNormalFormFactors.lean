import OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter
import OAI.RepresentationTheory.Weil.Local.TransposeSubstitution

/-! # Gaussian Normal Form Factors -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianNormalFormFactors.Construction

noncomputable section

/-! Determinant character factors in a Fourier normal form product. -/

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

theorem gaussianSquareCharacter_inv (a : kˣ) :
    GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns a⁻¹ =
      GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns a := by
  rw [map_inv]
  have h := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter_square hnd ψ hu hc hn hns a
  rw [pow_two] at h
  exact inv_eq_of_mul_eq_one_left h

theorem gaussianSquareCharacter_normalForm_product {n : ℕ} (B B' N : FunctionsMetaplectic.Construction.GeneralLinear k n) :
    let χ := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns
    χ (FunctionsMetaplectic.Construction.determinantUnit k N) *
      χ (FunctionsMetaplectic.Construction.determinantUnit k (B * (TransposeSubstitution.Construction.transposeGeneralLinear B')⁻¹ * N)) =
        χ (FunctionsMetaplectic.Construction.determinantUnit k B) * χ (FunctionsMetaplectic.Construction.determinantUnit k B') := by
  dsimp only
  rw [LinearOscillatorHom.Construction.determinantUnit_mul, LinearOscillatorHom.Construction.determinantUnit_mul, FourierLinearSubstitution.Construction.determinantUnit_inv, TransposeSubstitution.Construction.determinantUnit_transpose,
    map_mul, map_mul, gaussianSquareCharacter_inv]
  have h := GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter_square hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k N)
  rw [pow_two] at h
  rw [mul_comm _ (_ * _), mul_assoc, h, mul_one]

end

end OAI.RepresentationTheory.Weil.Local.GaussianNormalFormFactors.Construction
