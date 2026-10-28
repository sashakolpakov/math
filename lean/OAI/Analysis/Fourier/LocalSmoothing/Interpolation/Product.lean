import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Scale
import OAI.Analysis.Fourier.LocalSmoothing.L2

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation


theorem observation_norm_le_of_slices {n : ℕ} {u : Space n × ℝ → ℂ}
    (hu : Measurable u) {p : ℝ} (hp : 0 < p) {A : ℝ≥0∞}
    (hbound : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (fun x => u (x,t)) (.ofReal p) volume ≤ A) :
    eLpNorm u (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A := by
  have H : (∫⁻ z, ‖u z‖ₑ ^ p ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A ^ p := by
    rw [OAI.Analysis.Fourier.LocalSmoothing.observationMeasure, lintegral_prod_symm' _ (hu.enorm.pow_const p)]
    calc
      _ ≤ ∫⁻ t in Icc (1 : ℝ) 2, A ^ p := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
        have h := ENNReal.rpow_le_rpow (hbound t ht) hp.le
        have hm : Measurable (fun x : Space n => u (x,t)) :=
          hu.comp (measurable_id.prodMk measurable_const)
        rwa [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hm.aestronglyMeasurable] at h
      _ = _ := by norm_num [Real.volume_Icc]
  have H' := ENNReal.rpow_le_rpow H (show 0 ≤ 1 / p by positivity)
  simpa only [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hu.aestronglyMeasurable,
    ← ENNReal.rpow_mul, mul_one_div_cancel hp.ne', ENNReal.rpow_one] using H'

theorem observation_ae_time {n : ℕ} :
    ∀ᵐ z : Space n × ℝ ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n, z.2 ∈ Icc (1 : ℝ) 2 := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_Icc.preimage measurable_snd)).mpr
  exact Filter.Eventually.of_forall fun _ => ae_restrict_mem measurableSet_Icc

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
