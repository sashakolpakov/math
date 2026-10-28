import OAI.Analysis.PDE.WaveEquation.LowEstimate

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Dispersion


theorem eLpNorm_observation_le_of_slices {n : ℕ} {u v : Space n × ℝ → ℂ}
    (hu : Measurable u) (hv : Measurable v) {p : ℝ} (hp : 0<p)
    (hb : ∀ t ∈ Icc (1:ℝ) 2,
      eLpNorm (fun x ↦ u (x,t)) (ENNReal.ofReal p) volume ≤
        eLpNorm (fun x ↦ v (x,t)) (ENNReal.ofReal p) volume) :
    eLpNorm u (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      eLpNorm v (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
  have H : (∫⁻ z, ‖u z‖ₑ^p ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ∫⁻ z, ‖v z‖ₑ^p ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n := by
    rw [OAI.Analysis.Fourier.LocalSmoothing.observationMeasure,lintegral_prod_symm' _ (hu.enorm.pow_const p),
      lintegral_prod_symm' _ (hv.enorm.pow_const p)]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have Ht := ENNReal.rpow_le_rpow (hb t ht) hp.le
    have hum : Measurable (fun x : Space n ↦ u (x,t)) := hu.comp (measurable_id.prodMk measurable_const)
    have hvm : Measurable (fun x : Space n ↦ v (x,t)) := hv.comp (measurable_id.prodMk measurable_const)
    rwa [OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hum.aestronglyMeasurable,
      OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hvm.aestronglyMeasurable] at Ht
  have H' := ENNReal.rpow_le_rpow H (show 0≤1/p by positivity)
  simpa only [← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hu.aestronglyMeasurable,
    ← OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_rpow_eq_lintegral hp hv.aestronglyMeasurable,
    ← ENNReal.rpow_mul,mul_one_div_cancel hp.ne',ENNReal.rpow_one] using H'

theorem eLpNorm_observation_le_mul_of_slices {n : ℕ} {u v : Space n × ℝ → ℂ}
    (hu : Measurable u) (hv : Measurable v) {p C : ℝ} (hp : 0<p) (hC : 0≤C)
    (hb : ∀ t ∈ Icc (1:ℝ) 2,
      eLpNorm (fun x ↦ u (x,t)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (fun x ↦ v (x,t)) (ENNReal.ofReal p) volume) :
    eLpNorm u (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm v (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
  have H := eLpNorm_observation_le_of_slices hu (measurable_const.smul hv) hp
    (v := C • v) (fun t ht ↦ by
      change _ ≤ eLpNorm (C • (fun x : Space n ↦ v (x,t))) _ _
      rw [eLpNorm_const_smul,Real.enorm_eq_ofReal hC]
      exact hb t ht)
  simpa only [eLpNorm_const_smul,Real.enorm_eq_ofReal hC] using H

end OAI.Analysis.Fourier.Dispersion
