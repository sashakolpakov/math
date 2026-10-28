import OAI.RepresentationTheory.Weil.Local.RealCharacters
import OAI.RepresentationTheory.Weil.Local.FourierEquivalence

/-! # Real Normalization -/

namespace OAI.RepresentationTheory.Weil.Local.RealNormalization.Construction

noncomputable section

/-! The analytic clauses of LocalWeil for every continuous nontrivial unitary real character. -/

open _root_.MeasureTheory Filter
open scoped _root_.Topology ENNReal

theorem real_fourier_frequency {n : ℕ} (c : ℝ) (f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ)
    (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f x =
      FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f (c • x) := by
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    congr 1
    change (Real.fourierChar (c * -FunctionsMetaplectic.Construction.dot x y) : ℂ) =
      (Real.fourierChar (1 * -FunctionsMetaplectic.Construction.dot (c • x) y) : ℂ)
    congr 2
    simp [FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, mul_assoc]

theorem real_fourier_scaled_input {n : ℕ} (c : ℝ) (g : FunctionsMetaplectic.Construction.Position ℝ n → ℂ)
    (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume (fun y => g (c • y)) x =
      ((|c| ^ n)⁻¹ : ℝ) • FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume g x := by
  have h := Measure.integral_comp_smul (volume : Measure (FunctionsMetaplectic.Construction.Position ℝ n))
    (fun y => g y * Gaussian.Construction.realCharacter 1 (-FunctionsMetaplectic.Construction.dot x y)) c
  simp only [Module.finrank_pi, Fintype.card_fin, abs_inv, abs_pow] at h
  unfold FunctionsMetaplectic.Construction.fourierIntegral
  rw [← h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    dsimp only
    congr 1
    change (Real.fourierChar (c * -FunctionsMetaplectic.Construction.dot x y) : ℂ) =
      (Real.fourierChar (1 * -FunctionsMetaplectic.Construction.dot x (c • y)) : ℂ)
    congr 2
    simp [FunctionsMetaplectic.Construction.dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem real_fourier_square_volume {n : ℕ} (c : ℝ)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume
      (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f.val) x =
      ((|c| ^ n)⁻¹ : ℝ) • f.val (-x) := by
  have hf : FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f.val =
      fun y => FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter 1) volume f.val (c • y) :=
    funext (real_fourier_frequency c f.val)
  rw [hf, real_fourier_scaled_input, RealFourierLp.Construction.real_fourier_inversion_standard]

theorem positionMeasure_real (n : ℕ) (c : ℝ) (hc : c ≠ 0) :
    FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c) =
      ENNReal.ofReal (Real.sqrt |c| ^ n) • volume := by
  unfold FunctionsMetaplectic.Construction.positionMeasure
  simp_rw [RealFourierLp.Construction.selfDualMeasure_real c hc]
  let : (ENNReal.ofReal (Real.sqrt |c|) • (volume : Measure ℝ)).IsAddHaarMeasure := by
    apply Measure.IsAddHaarMeasure.smul
    · exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hc))).ne'
    · exact ENNReal.ofReal_ne_top
  refine Measure.pi_eq (μ := fun _ : Fin n =>
    ENNReal.ofReal (Real.sqrt |c|) • (volume : Measure ℝ)) fun s _ => ?_
  rw [Measure.smul_apply, volume_pi_pi]
  simp only [Measure.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (Real.sqrt_nonneg _)]

theorem fourierIntegral_real_normalized {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : FunctionsMetaplectic.Construction.Position ℝ n → ℂ) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f x =
      (Real.sqrt |c| ^ n : ℝ) • FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f x := by
  rw [positionMeasure_real n c hc, FunctionsMetaplectic.Construction.fourierIntegral, integral_smul_measure]
  rw [ENNReal.toReal_ofReal (by positivity)]
  rfl

theorem real_fourier_inversion {n : ℕ} (c : ℝ) (hc : c ≠ 0)
    (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n) :
    FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c))
      (FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val) x =
        f.val (-x) := by
  have hf : FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) (FunctionsMetaplectic.Construction.positionMeasure ℝ n (Gaussian.Construction.realCharacter c)) f.val =
      (Real.sqrt |c| ^ n : ℂ) • FunctionsMetaplectic.Construction.fourierIntegral (Gaussian.Construction.realCharacter c) volume f.val := by
    funext y
    rw [fourierIntegral_real_normalized c hc]
    simp only [Complex.real_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_pow]
  rw [fourierIntegral_real_normalized c hc, hf, FunctionsMetaplectic.Construction.fourierIntegral_smul,
    Pi.smul_apply, real_fourier_square_volume]
  simp only [Complex.real_smul, smul_eq_mul]
  have hcoef : (Real.sqrt |c| ^ n) * (Real.sqrt |c| ^ n) * (|c| ^ n)⁻¹ = 1 := by
    rw [← mul_pow, Real.mul_self_sqrt (abs_nonneg _), mul_inv_cancel₀ (pow_ne_zero _ (abs_ne_zero.mpr hc))]
  have hcoefC : (Real.sqrt |c| ^ n : ℂ) * (Real.sqrt |c| ^ n : ℂ) * (((|c| ^ n)⁻¹ : ℝ) : ℂ) = 1 := by
    exact_mod_cast hcoef
  calc
    _ = ((Real.sqrt |c| ^ n : ℂ) * (Real.sqrt |c| ^ n : ℂ) *
        (((|c| ^ n)⁻¹ : ℝ) : ℂ)) * f.val (-x) := by push_cast; ring
    _ = _ := by rw [hcoefC, one_mul]

/-- Positivity, Haar validity, nonzero Gaussian limits, the eighth-root identity,
and Fourier inversion follow from the original natural hypotheses at a real place. -/
theorem real_analytic_normalization
    (ψ : AddChar ℝ ℂ) (hc : Continuous (fun t => ψ t))
    (hu : ∀ t, ‖ψ t‖ = 1) (hn : ∃ t, ψ t ≠ 1) (n : ℕ) :
    0 < FunctionsMetaplectic.Construction.fourierHaarScaleSquared ℝ ψ ∧
    (FunctionsMetaplectic.Construction.selfDualMeasure ℝ ψ).IsAddHaarMeasure ∧
    (∀ a : ℝ, a ≠ 0 →
      Tendsto (FunctionsMetaplectic.Construction.regularizedGaussian ℝ ψ a) (𝓝[>] (0 : ℝ)) (𝓝 (FunctionsMetaplectic.Construction.gaussianIntegral ℝ ψ a)) ∧
      FunctionsMetaplectic.Construction.gaussianIntegral ℝ ψ a ≠ 0 ∧ FunctionsMetaplectic.Construction.gaussianIndex ℝ ψ a ^ 8 = 1) ∧
    (∀ (f : FunctionsMetaplectic.Construction.schwartzBruhat ℝ n) (x : FunctionsMetaplectic.Construction.Position ℝ n),
      FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ)
        (FunctionsMetaplectic.Construction.fourierIntegral ψ (FunctionsMetaplectic.Construction.positionMeasure ℝ n ψ) f.val) x = f.val (-x)) := by
  obtain ⟨c, hc', rfl⟩ := RealCharacters.Construction.continuous_nontrivial_unitary_real_character ψ hc hu hn
  refine ⟨RealFourierLp.Construction.fourierHaarScaleSquared_real_pos c hc',
    FourierTools.Construction.selfDualMeasure_isAddHaarMeasure_of_scale_pos ℝ (Gaussian.Construction.realCharacter c)
      (RealFourierLp.Construction.fourierHaarScaleSquared_real_pos c hc'), ?_, real_fourier_inversion c hc'⟩
  intro a ha
  refine ⟨?_, Gaussian.Construction.gaussianIntegral_real_ne_zero c a hc' ha, Gaussian.Construction.gaussianIndex_real_eighth_power c a hc' ha⟩
  rw [Gaussian.Construction.gaussianIntegral_real_eq c a hc' ha]
  exact Gaussian.Construction.regularizedGaussian_real_tendsto c a hc' ha

end

end OAI.RepresentationTheory.Weil.Local.RealNormalization.Construction
