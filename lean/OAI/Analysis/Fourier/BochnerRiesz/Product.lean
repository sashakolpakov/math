import OAI.Analysis.Fourier.BochnerRiesz.ShortTime
import OAI.Analysis.Fourier.BochnerRiesz.TimeDilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem lintegral_enorm_rpow_eq_eLpNorm_pow {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℂ} (hf : AEStronglyMeasurable f μ) {p : ℝ} (hp : 0 < p) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) = eLpNorm f (ENNReal.ofReal p) μ ^ p := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top hf,
    ENNReal.toReal_ofReal hp.le, ← ENNReal.rpow_mul, one_div_mul_cancel hp.ne', ENNReal.rpow_one]

theorem eLpNorm_prod_le_of_section_bound {n : ℕ} {F : Space n × ℝ → ℂ}
    (hF : Continuous F) {ν : Measure ℝ} [SFinite ν] {p : ℝ} (hp : 0 < p)
    {B : ℝ≥0∞} (hb : ∀ᵐ t ∂ν, eLpNorm (fun x ↦ F (x, t)) (ENNReal.ofReal p) volume ≤ B) :
    eLpNorm F (ENNReal.ofReal p) (volume.prod ν) ≤ ν Set.univ ^ (1 / p) * B := by
  have hmeas : AEMeasurable (fun z ↦ ‖F z‖ₑ ^ p) (volume.prod ν) :=
    hF.measurable.enorm.aemeasurable.pow_const p
  have hi : (∫⁻ z, ‖F z‖ₑ ^ p ∂volume.prod ν) ≤ ν Set.univ * B ^ p := by
    rw [lintegral_prod_symm _ hmeas]
    calc
      _ ≤ ∫⁻ t, B ^ p ∂ν := by
        apply lintegral_mono_ae
        filter_upwards [hb] with t ht
        have hm : AEStronglyMeasurable (fun x : Space n ↦ F (x, t)) volume :=
          (hF.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
        rw [lintegral_enorm_rpow_eq_eLpNorm_pow hm hp]
        exact ENNReal.rpow_le_rpow ht hp.le
      _ = _ := by simp [mul_comm]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by positivity) ENNReal.ofReal_ne_top
    hF.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le]
  calc
    _ ≤ (ν Set.univ * B ^ p) ^ (1 / p) := ENNReal.rpow_le_rpow hi (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
        mul_one_div_cancel hp.ne', ENNReal.rpow_one]

theorem shortTime_annular_slab {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (hzero : (0 : Space n) ∉ tsupport χ)
    {p : ℝ} (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h r : ℝ, 0 < r → r ≤ h →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ ≠ 0 → χ (h • ξ) = 1) →
      eLpNorm (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal p) (timeSlabMeasure n r) ≤
      ENNReal.ofReal (C * r ^ (1 / p)) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, hb⟩ := shortTime_annular_bound hχ hc hzero
  refine ⟨C, hC, ?_⟩
  intro h r hr hrh f hcut
  have hh : 0 < h := lt_of_lt_of_le hr hrh
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpone : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hb' : ∀ᵐ t ∂volume.restrict (Set.Icc r (2 * r)),
      eLpNorm (fun x ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have ht' : t / h ∈ Set.Icc (-2 : ℝ) 2 := by
      constructor
      · apply (le_div_iff₀ hh).mpr
        nlinarith [ht.1]
      · apply (div_le_iff₀ hh).mpr
        nlinarith [ht.2]
    simpa only [div_mul_cancel₀ _ hh.ne'] using
      hb h hh (t / h) ht' f f.integrable hcut _ hpone ENNReal.ofReal_ne_top
  have H := eLpNorm_prod_le_of_section_bound (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f) hp0 hb'
  have hv : volume.restrict (Set.Icc r (2 * r)) Set.univ = ENNReal.ofReal r := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc]
    congr 1
    ring
  rw [hv, ENNReal.ofReal_rpow_of_pos hr] at H
  simpa only [timeSlabMeasure, ENNReal.ofReal_mul hC, mul_assoc, mul_comm, mul_left_comm] using H

end OAI.Analysis.Fourier.BochnerRiesz
