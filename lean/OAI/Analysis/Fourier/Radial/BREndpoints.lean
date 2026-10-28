import OAI.Analysis.Fourier.Radial.BRIntegrable
import OAI.Analysis.Fourier.BochnerRiesz.RadiusDilation

open OAI.Analysis.Fourier.Wave

/-! The high-order Bochner--Riesz theorem including both endpoint spaces. -/

open _root_.MeasureTheory Metric Set Filter
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Radial

theorem hasCompactSupport_complex_bochnerRieszSymbol_unit {n : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun ξ : Space n => (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ : ℂ)) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Space n) 1)
  intro x hx
  have h : 1 < ‖x‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using hx
  simp only [bochnerRieszSymbol_unit_zero hδ h.le, Complex.ofReal_zero]

theorem eLpNorm_complexConvolution_top_le {n : ℕ} {k f : Space n → ℂ}
    (hk : AEStronglyMeasurable k volume) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (OAI.Analysis.Fourier.WavePackets.complexConvolution k f volume) ∞ volume ≤
      eLpNorm k 1 volume * eLpNorm f ∞ volume := by
  have hm := OAI.Analysis.Fourier.WavePackets.aestronglyMeasurable_complexConvolution hk hf
  rw [eLpNorm_exponent_top hm]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  apply Eventually.of_forall
  intro x
  have hbound : ∀ᵐ y ∂(volume : Measure (Space n)),
      ‖f (x - y)‖ₑ ≤ eLpNorm f ∞ volume := by
    have H := ((volume : Measure (Space n)).measurePreserving_sub_left x).quasiMeasurePreserving.ae
      (enorm_ae_le_eLpNormEssSup f volume)
    simpa only [eLpNorm_exponent_top hf] using H
  rw [eLpNorm_one_eq_lintegral_enorm hk]
  calc
    _ ≤ ∫⁻ y, ‖k y * f (x - y)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ y, ‖k y‖ₑ * eLpNorm f ∞ volume := by
      apply lintegral_mono_ae
      filter_upwards [hbound] with y hy
      rw [enorm_mul]
      exact mul_le_mul' le_rfl hy
    _ = _ := lintegral_mul_const'' _ hk.enorm

theorem eLpNorm_frequencyHalfWave_zero_top_le {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {f : Space n → ℂ} (hf : Integrable f) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f) ∞ volume ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume * eLpNorm f ∞ volume := by
  have hi : Integrable φ := hφ.integrable_of_hasCompactSupport hc
  have hscaled : Integrable (fun ξ => φ (h • ξ)) :=
    (hφ.comp (continuous_const.smul continuous_id)).integrable_of_hasCompactSupport
      (hc.comp_smul hh.ne')
  have he : OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f = OAI.Analysis.Fourier.WavePackets.complexConvolution
      (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => φ (h • ξ))) f volume := by
    funext x
    exact OAI.Analysis.Fourier.BochnerRiesz.frequencyHalfWave_zero_eq_convolution hφ hc hh hf x
  rw [he, ← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_angularInverse_dilate_one hi hh]
  exact eLpNorm_complexConvolution_top_le
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse hscaled).aestronglyMeasurable hf.aestronglyMeasurable

theorem aestronglyMeasurable_frequencyHalfWave_zero {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {f : Space n → ℂ} (hf : Integrable f) :
    AEStronglyMeasurable (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f) volume := by
  have hi : Integrable (fun ξ => φ (h • ξ)) :=
    (hφ.comp (continuous_const.smul continuous_id)).integrable_of_hasCompactSupport
      (hc.comp_smul hh.ne')
  have he : OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f = OAI.Analysis.Fourier.WavePackets.complexConvolution
      (OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ => φ (h • ξ))) f volume := by
    funext x
    exact OAI.Analysis.Fourier.BochnerRiesz.frequencyHalfWave_zero_eq_convolution hφ hc hh hf x
  rw [he]
  exact OAI.Analysis.Fourier.WavePackets.aestronglyMeasurable_complexConvolution
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_angularInverse hi).aestronglyMeasurable hf.aestronglyMeasurable

theorem eLpNorm_frequencyHalfWave_zero_all_le {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    {f : Space n → ℂ} (hf : Integrable f) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h 0 f) p volume ≤
      eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume * eLpNorm f p volume := by
  by_cases ht : p = ∞
  · subst p
    exact eLpNorm_frequencyHalfWave_zero_top_le hφ hc hh hf
  · exact OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_frequencyHalfWave_zero_le hφ hc hh hf hp ht

theorem bochnerRiesz_high_order_all_exponents {n : ℕ} (hn : 1 ≤ n) {δ : ℝ}
    (hδ : ((n : ℝ) - 1) / 2 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ≥0∞, 1 ≤ p → ∀ R : ℝ, 0 < R →
      ∀ f : SchwartzMap (Space n) ℂ,
        MemLp (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ∧
        eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ≤
          ENNReal.ofReal C * eLpNorm f p volume := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < δ := by linarith
  let φ : Space n → ℂ := fun ξ => OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ
  have hφ : Continuous φ := Complex.continuous_ofReal.comp
    (OAI.Analysis.Fourier.BochnerRiesz.continuous_bochnerRieszSymbol hd.le 1)
  have hc : HasCompactSupport φ := hasCompactSupport_complex_bochnerRieszSymbol_unit hd
  let A := eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.angularInverse φ) 1 volume
  have hA : A ≠ ∞ := (memLp_one_iff_integrable.mpr (integrable_bochnerRieszKernel hn hδ)).eLpNorm_ne_top
  have hb : A ≤ ENNReal.ofReal (A.toReal + 1) := by
    calc
      A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA).symm
      _ ≤ ENNReal.ofReal (A.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)
  refine ⟨A.toReal + 1, by positivity, fun p hp R hR f => ?_⟩
  have he := OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz_eq_frequencyHalfWave δ hR f
  have H : eLpNorm (OAI.Analysis.Fourier.BochnerRiesz.bochnerRiesz δ R f) p volume ≤ A * eLpNorm f p volume := by
    rw [he]
    exact eLpNorm_frequencyHalfWave_zero_all_le hφ hc (inv_pos.mpr hR) f.integrable hp
  have H' := H.trans (mul_le_mul' hb le_rfl)
  exact ⟨H'.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (f.memLp p volume).eLpNorm_lt_top), H'⟩

end OAI.Analysis.Fourier.Radial
