import OAI.RepresentationTheory.Weil.Local.GaussianSquareCharacter
import OAI.RepresentationTheory.Weil.Local.TransposeSubstitution

/-! # Gaussian Determinant Square -/

namespace OAI.RepresentationTheory.Weil.Local.GaussianDeterminantSquare.Construction

noncomputable section

/-! Squared diagonal Gaussian coefficients depend only on dimension and determinant. -/

open _root_.Matrix

variable {k : Type} [NormedField k] [CompleteSpace k] [LocallyCompactSpace k]
  [NonarchimedeanAddGroup k] [CharZero k] [MeasurableSpace k] [BorelSpace k]
  (hnd : ¬ DiscreteTopology k) (ψ : AddChar k ℂ) (hu : ∀ t : k, ‖ψ t‖ = 1)
  (hc : Continuous (fun t => ψ t)) (hn : ∃ t : k, ψ t ≠ 1)
  (hns : ¬ ∃ t : k, t ^ 2 = -1)

include hnd hu hc hn in
theorem gaussianIndex_sq_eq_character_mul (a : kˣ) :
    FunctionsMetaplectic.Construction.gaussianIndex k ψ a.val ^ 2 =
      (GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns a).val * FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ 2 := by
  have hz : FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ≠ 0 := FunctionsMetaplectic.Construction.phase_ne_zero
    (GaussianCompact.Construction.nonarchimedean_gaussian_limit_nonzero hnd ψ hu hc hn 1 one_ne_zero).2
  rw [GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter_apply, div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hz)]

theorem gaussianIndex_product_sq {n : ℕ} (a : Fin n → kˣ) :
    (∏ i, FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val) ^ 2 =
      (GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (∏ i, a i)).val *
        FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) := by
  let χ : kˣ →* ℂ := (Units.coeHom ℂ).comp (GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns)
  have he (i : Fin n) : FunctionsMetaplectic.Construction.gaussianIndex k ψ (a i).val ^ 2 = χ (a i) * FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ 2 :=
    gaussianIndex_sq_eq_character_mul hnd ψ hu hc hn hns (a i)
  rw [← Finset.prod_pow]
  simp_rw [he]
  rw [Finset.prod_mul_distrib, ← map_prod χ, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rfl

theorem diagonalGaussianCoefficient_square {n : ℕ} (a : Fin n → kˣ) :
    DiagonalQuadratic.Construction.diagonalGaussianCoefficient ψ a ^ 2 =
      (FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n) *
        (GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k (DiagonalAlgebra.Construction.diagonalGeneralLinear a))).val) /
          (FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k (DiagonalAlgebra.Construction.diagonalGeneralLinear a)) : ℂ) := by
  let d := FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k (DiagonalAlgebra.Construction.diagonalGeneralLinear a))
  have hd : 0 < d := FunctionsMetaplectic.Construction.localModulus_pos k _
  have hs : ((Real.sqrt d : ℂ)⁻¹) ^ 2 = (d : ℂ)⁻¹ := by
    rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt hd.le]
  rw [DiagonalAlgebra.Construction.diagonalGaussianCoefficient_eq, mul_pow, gaussianIndex_product_sq hnd ψ hu hc hn hns a]
  change (_ * FunctionsMetaplectic.Construction.gaussianIndex k ψ 1 ^ (2 * n)) * ((Real.sqrt d : ℂ)⁻¹) ^ 2 = _
  rw [hs, DiagonalAlgebra.Construction.diagonalGeneralLinear_determinant, div_eq_mul_inv]
  dsimp only [d]
  rw [DiagonalAlgebra.Construction.diagonalGeneralLinear_determinant]
  ring

omit [CompleteSpace k] [NonarchimedeanAddGroup k] [CharZero k] in
theorem determinantUnit_congruence {n : ℕ} (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) :
    FunctionsMetaplectic.Construction.determinantUnit k (DiagonalAlgebra.Construction.diagonalGeneralLinear a) = FunctionsMetaplectic.Construction.determinantUnit k A ^ 2 * FunctionsMetaplectic.Construction.determinantUnit k M := by
  have he : TransposeSubstitution.Construction.transposeGeneralLinear A * M * A = DiagonalAlgebra.Construction.diagonalGeneralLinear a := Units.ext h
  rw [← he, LinearOscillatorHom.Construction.determinantUnit_mul, LinearOscillatorHom.Construction.determinantUnit_mul, TransposeSubstitution.Construction.determinantUnit_transpose, pow_two]
  ac_rfl

omit [CompleteSpace k] [NonarchimedeanAddGroup k] [CharZero k] in
theorem localModulus_congruence {n : ℕ} (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) :
    FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k (DiagonalAlgebra.Construction.diagonalGeneralLinear a)) =
      FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k A) ^ 2 * FunctionsMetaplectic.Construction.localModulus k (FunctionsMetaplectic.Construction.determinantUnit k M) := by
  rw [determinantUnit_congruence M A a h, pow_two, FunctionsMetaplectic.Construction.localModulus_mul, FunctionsMetaplectic.Construction.localModulus_mul]
  ring

theorem gaussianSquareCharacter_congruence {n : ℕ} (M A : FunctionsMetaplectic.Construction.GeneralLinear k n) (a : Fin n → kˣ)
    (h : A.val.transpose * M.val * A.val = diagonal (fun i => (a i).val)) :
    GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k (DiagonalAlgebra.Construction.diagonalGeneralLinear a)) =
      GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter hnd ψ hu hc hn hns (FunctionsMetaplectic.Construction.determinantUnit k M) := by
  rw [determinantUnit_congruence M A a h, map_mul, map_pow,
    GaussianSquareCharacter.Construction.nonarchimedeanGaussianSquareCharacter_square, one_mul]

end

end OAI.RepresentationTheory.Weil.Local.GaussianDeterminantSquare.Construction
