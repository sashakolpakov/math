import OAI.Analysis.Fourier.BochnerRiesz.ProjectionDilation
import OAI.Analysis.Fourier.BochnerRiesz.Basic

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem bochnerRiesz_eq_frequencyHalfWave {n : ℕ} (δ : ℝ) {R : ℝ} (hR : 0 < R)
    (f : Space n → ℂ) : OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave (fun ξ : Space n ↦ (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ : ℂ)) R⁻¹ 0 f := by
  funext x
  unfold OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave
  congr 1
  funext ξ
  simp only [zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul,
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR),
    div_one, Complex.real_smul]
  rw [div_eq_mul_inv, mul_comm ‖ξ‖ R⁻¹]

theorem bochnerRiesz_unit_schwartzDilate {n : ℕ} (δ : ℝ) {R : ℝ} (hR : 0 < R)
    (f : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ 1 (schwartzDilate R⁻¹ (inv_ne_zero hR.ne') f) =
      fun x ↦ OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f (R⁻¹ • x) := by
  rw [bochnerRiesz_eq_frequencyHalfWave δ (show (0 : ℝ) < 1 by norm_num),
    bochnerRiesz_eq_frequencyHalfWave δ hR]
  funext x
  change OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave _ (1 : ℝ)⁻¹ 0 (fun y ↦ f (R⁻¹ • y)) x = _
  rw [frequencyHalfWave_zero_dilate _ _ _ (inv_pos.mpr hR)]
  simp only [inv_one, one_mul]

theorem bochnerRiesz_uniform_radius_of_unit {n : ℕ} {δ : ℝ} {p : ℝ≥0∞} {C : ℝ}
    (hunit : ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ 1 f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume)
    {R : ℝ} (hR : 0 < R) (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ≤ ENNReal.ofReal C * eLpNorm f p volume := by
  have H := hunit (schwartzDilate R⁻¹ (inv_ne_zero hR.ne') f)
  rw [bochnerRiesz_unit_schwartzDilate δ hR f,
    eLpNorm_dilate_enormed _ _ (inv_pos.mpr hR),
    eLpNorm_schwartzDilate f p (inv_pos.mpr hR)] at H
  let D : ℝ≥0∞ := ENNReal.ofReal (((R⁻¹) ^ n)⁻¹) ^ (1 / p.toReal)
  have hD0 : D ≠ 0 := by dsimp [D]; positivity
  have hDt : D ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · positivity
    · exact ENNReal.ofReal_ne_top
  change D * _ ≤ ENNReal.ofReal C * (D * _) at H
  have H' := mul_le_mul' (le_refl D⁻¹) H
  simpa only [← mul_assoc, ENNReal.inv_mul_cancel hD0 hDt, one_mul,
    show D⁻¹ * ENNReal.ofReal C * D = ENNReal.ofReal C from by
      rw [mul_right_comm, ENNReal.inv_mul_cancel hD0 hDt, one_mul]] using H'

end OAI.Analysis.Fourier.BochnerRiesz
