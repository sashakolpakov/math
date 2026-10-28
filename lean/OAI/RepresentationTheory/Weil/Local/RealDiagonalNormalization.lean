import OAI.RepresentationTheory.Weil.Local.RealDiagonalFresnel
import OAI.RepresentationTheory.Weil.Local.RealFresnelNormalization

/-! # Real Diagonal Normalization -/

namespace OAI.RepresentationTheory.Weil.Local.RealDiagonalNormalization.Construction

noncomputable section

/-! Exact Gaussian coefficients for diagonal real reflections. -/

open _root_.MeasureTheory

theorem gaussianIndex_real_character_mul (c a : ℝ) (hc : c ≠ 0) (ha : a ≠ 0) :
    FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter (c * a)) 1 = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) a := by
  rw [Gaussian.Construction.gaussianIndex_real_eq (c * a) 1 (mul_ne_zero hc ha) one_ne_zero,
    Gaussian.Construction.gaussianIndex_real_eq c a hc ha]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_mul]

theorem real_reflection_gaussian_coefficient {n : ℕ}
    (c : ℝ) (hc : c ≠ 0) (a : Fin n → ℝ) (ha : ∀ i, a i ^ 2 = 1) :
    (Real.sqrt |c| : ℂ) ^ n * RealDiagonalFresnel.Construction.realDiagonalGaussianCoefficient c a =
      ∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i) := by
  have hai (i : Fin n) : a i ≠ 0 := by
    intro h
    have hi := ha i
    rw [h, zero_pow (by decide)] at hi
    exact zero_ne_one hi
  have habs (i : Fin n) : |a i| = 1 := by
    apply (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp
    rw [sq_abs, ha i, one_pow]
  have hcoef (i : Fin n) : (Real.sqrt |c| : ℂ) *
      (Complex.I / ((c * a i : ℝ) : ℂ)) ^ (1 / 2 : ℂ) = FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i) := by
    have h := RealFresnelNormalization.Construction.realGaussian_coefficient_normalized (c * a i) (mul_ne_zero hc (hai i))
    rwa [abs_mul, habs i, mul_one, gaussianIndex_real_character_mul c (a i) hc (hai i)] at h
  calc
    _ = ∏ i, (Real.sqrt |c| : ℂ) * (Complex.I / ((c * a i : ℝ) : ℂ)) ^ (1 / 2 : ℂ) := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, RealDiagonalFresnel.Construction.realDiagonalGaussianCoefficient]
    _ = _ := Finset.prod_congr rfl (fun i _ => hcoef i)

theorem real_fourier_volume_integrable {n : ℕ} (c : ℝ) (hc : c ≠ 0) (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    Integrable (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f.val) := by
  have h := FunctionsMetaplectic.Construction.schwartzBruhat_integrable volume
    ((FunctionsMetaplectic.Construction.schwartzBruhat_coordinateEquiv (RealFourierFamily.Construction.realFrequencyAddEquiv n c hc)) (RealFourierLp.Construction.realBruhatFourier n f))
  convert! h using 1
  funext x
  rw [RealNormalization.Construction.real_fourier_frequency, ← RealFourierLp.Construction.realBruhatFourier_apply]
  rfl

theorem real_reflection_fresnel_pairing {n : ℕ}
    (c : ℝ) (hc : c ≠ 0) (a : Fin n → ℝ) (ha : ∀ i, a i ^ 2 = 1)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) :
    (∫ x, FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val x *
      Gaussian.Construction.realCharacter c (FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal a) x) ∂ FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) =
      (∏ i, FunctionsMetaplectic.Construction.gaussianIndex ℝ (Gaussian.Construction.realCharacter c) (a i)) *
        ∫ x, f.val x * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal a) x)
          ∂ FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c) := by
  have hai (i : Fin n) : a i ≠ 0 := by
    intro h
    have hi := ha i
    rw [h, zero_pow (by decide)] at hi
    exact zero_ne_one hi
  have hinv (i : Fin n) : (a i)⁻¹ = a i := by
    apply inv_eq_of_mul_eq_one_right
    exact (pow_two (a i)).symm.trans (ha i)
  have hp := RealDiagonalFresnel.Construction.real_diagonal_fresnel_pairing_volume c hc a hai
    (FunctionsMetaplectic.Construction.schwartzBruhat_integrable volume f) (real_fourier_volume_integrable c hc f)
  simp_rw [hinv] at hp
  simp_rw [RealNormalization.Construction.fourierIntegral_real_normalized c hc, Complex.real_smul]
  rw [RealNormalization.Construction.positionMeasure_real n c hc, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [Complex.real_smul, mul_assoc, integral_const_mul]
  rw [hp]
  push_cast
  calc
    _ = ((Real.sqrt |c| : ℂ) ^ n * RealDiagonalFresnel.Construction.realDiagonalGaussianCoefficient c a) *
        ((Real.sqrt |c| : ℂ) ^ n * ∫ x, f.val x * Gaussian.Construction.realCharacter c (-FunctionsMetaplectic.Construction.quadratic (Matrix.diagonal a) x)) := by ring
    _ = _ := by rw [real_reflection_gaussian_coefficient c hc a ha]

end

end OAI.RepresentationTheory.Weil.Local.RealDiagonalNormalization.Construction
