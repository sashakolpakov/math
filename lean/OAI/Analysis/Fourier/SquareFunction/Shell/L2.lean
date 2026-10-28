import OAI.Analysis.Fourier.SquareFunction.Shell.Mixed
import OAI.Analysis.Fourier.Wave.Schwartz

open OAI.Analysis.Fourier.Wave

/-! Exact Plancherel energy for the thin-shell square function. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal

theorem eLpNorm_two_rpow_general {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] (μ : Measure X) {g : X → H}
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  change ((∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = _
  rw [← ENNReal.rpow_mul]
  norm_num

theorem lintegral_dilate_real (g : ℝ → ℝ≥0∞) (hg : Measurable g)
    {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ t : ℝ, g (δ * t)) = ENNReal.ofReal δ⁻¹ * ∫⁻ t : ℝ, g t := by
  have hm : Measure.map (fun t : ℝ => δ * t) volume = ENNReal.ofReal δ⁻¹ • volume := by
    simpa [smul_eq_mul, abs_of_pos (inv_pos.mpr hδ)] using
      Measure.map_addHaar_smul (volume : Measure ℝ) hδ.ne'
  have hd : Measurable (fun t : ℝ => δ * t) := measurable_const.mul measurable_id
  have hh := lintegral_map' (μ := (volume : Measure ℝ)) hg.aemeasurable hd.aemeasurable
  rw [hm, lintegral_smul_measure] at hh
  exact hh.symm

theorem lintegral_enorm_two_eq_ofReal_integral {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] {μ : Measure X} {g : X → H} (hg : MemLp g 2 μ) :
    (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) = ENNReal.ofReal (∫ x, ‖g x‖ ^ 2 ∂μ) := by
  have hi := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => sq_nonneg ‖g x‖)]
  apply lintegral_congr
  intro x
  rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg _) 2, ofReal_norm]

theorem halfWaveIntegral_lintegral_two {n : ℕ} (t : ℝ) (f : SchwartzMap (Space n) ℂ) :
    (∫⁻ x : Space n, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ)) =
      eLpNorm f 2 volume ^ (2 : ℝ) := by
  rw [lintegral_enorm_two_eq_ofReal_integral (OAI.Analysis.Fourier.Wave.memLp_halfWaveIntegral_two t f),
    OAI.Analysis.Fourier.Wave.halfWaveIntegral_energy t f, eLpNorm_two_rpow_general volume f.continuous.aestronglyMeasurable]
  exact (lintegral_enorm_two_eq_ofReal_integral (μ := volume) (f.memLp 2)).symm

theorem weighted_energy_of_slice_energy {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [SFinite μ] (w : ℝ → ℂ) (hw : Measurable w)
    (F : X × ℝ → ℂ) (hF : Measurable F) (B : ℝ≥0∞)
    (hB : ∀ t, (∫⁻ x, ‖F (x, t)‖ₑ ^ (2 : ℝ) ∂μ) = B) :
    (∫⁻ x, (∫⁻ t : ℝ, ‖w t * F (x, t)‖ₑ ^ (2 : ℝ)) ∂μ) =
      (∫⁻ t : ℝ, ‖w t‖ₑ ^ (2 : ℝ)) * B := by
  have hm : Measurable (fun z : X × ℝ => w z.2 * F z) :=
    (hw.comp measurable_snd).mul hF
  rw [lintegral_lintegral_swap (hm.enorm.pow_const (2 : ℝ)).aemeasurable]
  simp_rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  have hi (t : ℝ) : (∫⁻ x, ‖w t‖ₑ ^ (2 : ℝ) * ‖F (x, t)‖ₑ ^ (2 : ℝ) ∂μ) =
      ‖w t‖ₑ ^ (2 : ℝ) * B := by
    have ht : Measurable (fun x : X => F (x, t)) := hF.comp (measurable_id.prodMk measurable_const)
    exact (lintegral_const_mul _ (ht.enorm.pow_const (2 : ℝ))).trans
      (congrArg (fun z => ‖w t‖ₑ ^ (2 : ℝ) * z) (hB t))
  simp_rw [hi]
  exact lintegral_mul_const _ (hw.enorm.pow_const (2 : ℝ))

theorem weighted_halfWave_energy {n : ℕ} (w : ℝ → ℂ) (hw : Measurable w)
    (f : SchwartzMap (Space n) ℂ) :
    (∫⁻ x : Space n, ∫⁻ t : ℝ, ‖w t * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ)) =
      (∫⁻ t : ℝ, ‖w t‖ₑ ^ (2 : ℝ)) * eLpNorm f 2 volume ^ (2 : ℝ) :=
  weighted_energy_of_slice_energy volume w hw (fun z => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
    (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).measurable _ (fun t => halfWaveIntegral_lintegral_two t f)

theorem thinShellSquareNorm_energy {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) :
    (∫⁻ x : Space n, ‖thinShellSquareNorm φ δ f x‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal δ * eLpNorm φ 2 volume ^ (2 : ℝ) * eLpNorm f 2 volume ^ (2 : ℝ) := by
  let w : ℝ → ℂ := fun t => (𝓕 φ : SchwartzMap ℝ ℂ) (δ * t)
  have hw : Measurable w := (𝓕 φ : SchwartzMap ℝ ℂ).continuous.measurable.comp
    (measurable_const.mul measurable_id)
  have hm : Measurable (fun z : Space n × ℝ => w z.2 * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) :=
    (hw.comp measurable_snd).mul (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).measurable
  simp_rw [thinShellSquareNorm_sq φ hδ f]
  rw [lintegral_const_mul _ (hm.enorm.pow_const (2 : ℝ)).lintegral_prod_right]
  rw [weighted_halfWave_energy w hw f]
  have hwt : (∫⁻ t : ℝ, ‖w t‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal δ⁻¹ * eLpNorm φ 2 volume ^ (2 : ℝ) := by
    rw [show (fun t => ‖w t‖ₑ ^ (2 : ℝ)) =
      (fun t => ‖(𝓕 φ : SchwartzMap ℝ ℂ) (δ * t)‖ₑ ^ (2 : ℝ)) from rfl]
    rw [lintegral_dilate_real _ ((𝓕 φ : SchwartzMap ℝ ℂ).continuous.measurable.enorm.pow_const (2 : ℝ)) hδ,
      ← eLpNorm_two_rpow_general volume (𝓕 φ : SchwartzMap ℝ ℂ).continuous.aestronglyMeasurable,
      SchwartzMap.fourier_coe, eLpNorm_fourier_line φ.integrable (φ.memLp 2)]
  rw [hwt]
  have hc : ENNReal.ofReal δ ^ (2 : ℝ) * ENNReal.ofReal δ⁻¹ = ENNReal.ofReal δ := by
    rw [ENNReal.rpow_two, pow_two, ← ENNReal.ofReal_mul hδ.le,
      ← ENNReal.ofReal_mul (mul_nonneg hδ.le hδ.le), mul_inv_cancel_right₀ hδ.ne']
  calc
    _ = (ENNReal.ofReal δ ^ (2 : ℝ) * ENNReal.ofReal δ⁻¹) *
        eLpNorm φ 2 volume ^ (2 : ℝ) * eLpNorm f 2 volume ^ (2 : ℝ) := by ac_rfl
    _ = _ := by rw [hc]

theorem eLpNorm_thinShellSquareNorm_two {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) :
    eLpNorm (thinShellSquareNorm φ δ f) 2 volume =
      ENNReal.ofReal δ ^ (1 / 2 : ℝ) * eLpNorm φ 2 volume * eLpNorm f 2 volume := by
  have h := congrArg (fun z : ℝ≥0∞ => z ^ (1 / 2 : ℝ)) (thinShellSquareNorm_energy φ hδ f)
  rw [← eLpNorm_two_rpow_general volume (measurable_thinShellSquareNorm φ hδ f).aestronglyMeasurable,
    ← ENNReal.rpow_mul] at h
  have he : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  rw [he, ENNReal.rpow_one] at h
  refine h.trans ?_
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.rpow_mul, he, ENNReal.rpow_one]

theorem memLp_thinShellSquareNorm_two {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    {δ : ℝ} (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) :
    MemLp (thinShellSquareNorm φ δ f) 2 volume := by
  change eLpNorm (thinShellSquareNorm φ δ f) 2 volume < ⊤
  rw [eLpNorm_thinShellSquareNorm_two φ hδ f]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
    (φ.memLp 2).eLpNorm_lt_top) (f.memLp 2).eLpNorm_lt_top

end OAI.Analysis.Fourier.SquareFunction
