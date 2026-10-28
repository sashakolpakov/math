import OAI.Analysis.Fourier.Restriction.Polar
import OAI.MeasureTheory.Kakeya.Maximal

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped ENNReal

/-- Polar integration gives the correct volume scale for a shell without
subtracting two ball volumes. -/
theorem shell_lintegral_lower {n : ℕ} (hn : 1 ≤ n) {F : Space n → ℝ≥0∞}
    (hF : Measurable F) {t w : ℝ} (ht : 0 < t) (_ : 0 ≤ w) (q : ℝ≥0∞)
    (hbound : ∀ x : Space n, t ≤ ‖x‖ → ‖x‖ ≤ t+w → q ≤ F x) :
    ENNReal.ofReal w * ENNReal.ofReal (t^(n-1)) *
      (OAI.Analysis.Fourier.Restriction.sphereMeasure n) univ * q ≤ ∫⁻ x, F x := by
  rw [OAI.Analysis.Fourier.Restriction.lintegral_polar_sphereMeasure hn hF]
  have hinner : ∀ᵐ z ∂OAI.Analysis.Fourier.Restriction.sphereMeasure n,
      ENNReal.ofReal w * ENNReal.ofReal (t^(n-1)) * q ≤
        ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (r^(n-1))*F (r • z) := by
    filter_upwards [OAI.MeasureTheory.Kakeya.ae_sphereMeasure_norm n] with z hz
    calc
      _ = ∫⁻ r in Icc t (t+w), ENNReal.ofReal (t^(n-1))*q := by
        rw [lintegral_const,Measure.restrict_apply_univ,Real.volume_Icc]
        simp only [add_sub_cancel_left]
        ac_rfl
      _ ≤ ∫⁻ r in Icc t (t+w), ENNReal.ofReal (r^(n-1))*F (r • z) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
        have hr0 : 0 < r := ht.trans_le hr.1
        have hnorm : ‖r • z‖ = r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr0,hz,mul_one]
        apply mul_le_mul'
        · exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ht.le hr.1 _)
        · exact hbound (r • z) (by simpa only [hnorm] using hr.1) (by simpa only [hnorm] using hr.2)
      _ ≤ _ := lintegral_mono_set (fun r hr => ht.trans_le hr.1)
  have h := lintegral_mono_ae hinner
  rw [lintegral_const] at h
  convert h using 1 ; ac_rfl

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
