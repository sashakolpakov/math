import OAI.Analysis.Fourier.SquareFunction.Square.TimeHolder
import OAI.Analysis.Fourier.BochnerRiesz.TimeDecay
import OAI.Analysis.Fourier.BochnerRiesz.Shell.Time
import OAI.Analysis.Fourier.BochnerRiesz.Shell.Formula

open OAI.Analysis.Fourier.Wave

/-! The actual mixed spatial-Lᵖ/radius-L² norm of the thin shell. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory FourierTransform
open scoped ENNReal

noncomputable def thinShellSquareNorm {n : ℕ} (φ : SchwartzMap ℝ ℂ) (δ : ℝ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) : ℝ :=
  (eLpNorm (thinShellCycles φ δ f x) 2 volume).toReal

theorem enorm_thinShellSquareNorm {n : ℕ} (φ : SchwartzMap ℝ ℂ) {δ : ℝ} (hδ : 0 < δ)
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖thinShellSquareNorm φ δ f x‖ₑ = eLpNorm (thinShellCycles φ δ f x) 2 volume := by
  rw [thinShellSquareNorm, Real.enorm_eq_ofReal ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (memLp_thinShellCycles φ hδ f x).eLpNorm_ne_top]

theorem eLpNorm_two_rpow {g : ℝ → ℂ} (hg : Measurable g) :
    eLpNorm g 2 volume ^ (2 : ℝ) = ∫⁻ t : ℝ, ‖g t‖ₑ ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg.aestronglyMeasurable]
  change ((∫⁻ t : ℝ, ‖g t‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = _
  rw [← ENNReal.rpow_mul]
  norm_num

theorem measurable_slice_eLpNorm_two {n : ℕ} {F : Space n × ℝ → ℂ} (hF : Measurable F) :
    Measurable (fun x => eLpNorm (fun t => F (x, t)) 2 volume) := by
  have he : (fun x => eLpNorm (fun t => F (x, t)) 2 volume) =
      fun x => (∫⁻ t : ℝ, ‖F (x, t)‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    funext x
    have hs : Measurable (fun t : ℝ => F (x, t)) :=
      hF.comp (measurable_const.prodMk measurable_id)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
      hs.aestronglyMeasurable]
    norm_num
  rw [he]
  exact (hF.enorm.pow_const (2 : ℝ)).lintegral_prod_right.pow_const _

theorem measurable_thinShellSquareNorm {n : ℕ} (φ : SchwartzMap ℝ ℂ) {δ : ℝ}
    (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) :
    Measurable (thinShellSquareNorm φ δ f) := by
  have hF : Measurable (fun z : Space n × ℝ =>
      (𝓕 φ : SchwartzMap ℝ ℂ) (δ * z.2) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) :=
    ((𝓕 φ : SchwartzMap ℝ ℂ).continuous.measurable.comp
      (measurable_const.mul measurable_snd)).mul (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).measurable
  have he : thinShellSquareNorm φ δ f = fun x => (ENNReal.ofReal δ *
      eLpNorm (fun t : ℝ => (𝓕 φ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x) 2 volume).toReal := by
    funext x
    rw [thinShellSquareNorm, thinShellCycles_radius_L2_identity φ hδ f x]
  rw [he]
  exact ((measurable_slice_eLpNorm_two hF).const_mul _).ennreal_toReal

theorem lintegral_timeDensity_dilate {δ : ℝ} (hδ : 0 < δ) :
    (∫⁻ t : ℝ, OAI.Analysis.Fourier.BochnerRiesz.timeDensity (δ * t)) =
      ENNReal.ofReal δ⁻¹ * ∫⁻ t : ℝ, OAI.Analysis.Fourier.BochnerRiesz.timeDensity t := by
  have hm : Measure.map (fun t : ℝ => δ * t) volume = ENNReal.ofReal δ⁻¹ • volume := by
    simpa [smul_eq_mul, abs_of_pos (inv_pos.mpr hδ)] using
      Measure.map_addHaar_smul (volume : Measure ℝ) hδ.ne'
  have hd : Measurable (fun t : ℝ => δ * t) := measurable_const.mul measurable_id
  have hh := lintegral_map' (μ := (volume : Measure ℝ))
    OAI.Analysis.Fourier.BochnerRiesz.measurable_timeDensity.aemeasurable hd.aemeasurable
  rw [hm, lintegral_smul_measure] at hh
  exact hh.symm

theorem thinShellSquareNorm_sq {n : ℕ} (φ : SchwartzMap ℝ ℂ) {δ : ℝ}
    (hδ : 0 < δ) (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖thinShellSquareNorm φ δ f x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal δ ^ (2 : ℝ) *
      ∫⁻ t : ℝ, ‖(𝓕 φ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ) := by
  rw [enorm_thinShellSquareNorm φ hδ f x, thinShellCycles_radius_L2_identity φ hδ f x,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2), eLpNorm_two_rpow]
  exact ((𝓕 φ : SchwartzMap ℝ ℂ).continuous.measurable.comp
    (measurable_const.mul measurable_id)).mul (OAI.Analysis.Fourier.BochnerRiesz.continuous_time_halfWave f x).measurable

theorem thinShell_square_decay_domination {n : ℕ} (φ : SchwartzMap ℝ ℂ) {δ A M : ℝ}
    (hδ : 0 < δ) (hA : 0 ≤ A)
    (hφ : ∀ t : ℝ, ‖(𝓕 φ : SchwartzMap ℝ ℂ) t‖ ≤
      A * (1 + |t|) ^ (-2 : ℝ) * (1 + |t|) ^ (-M))
    (f : SchwartzMap (Space n) ℂ) (x : Space n) :
    ‖thinShellSquareNorm φ δ f x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal (δ * A) ^ (2 : ℝ) * ∫⁻ t : ℝ, OAI.Analysis.Fourier.BochnerRiesz.timeDensity (δ * t) *
        ‖(1 + |δ * t|) ^ (-M) • OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ) := by
  let F := fun t : ℝ => (1 + |δ * t|) ^ (-M) • OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x
  have hFm : Measurable F := by
    have hw : Continuous (fun t : ℝ => (1 + |δ * t|) ^ (-M)) := by
      apply Continuous.rpow_const (by fun_prop)
      intro t
      left
      positivity
    exact hw.measurable.smul (OAI.Analysis.Fourier.BochnerRiesz.continuous_time_halfWave f x).measurable
  have hk : Measurable (fun t : ℝ => OAI.Analysis.Fourier.BochnerRiesz.timeDensity (δ * t)) :=
    OAI.Analysis.Fourier.BochnerRiesz.measurable_timeDensity.comp (measurable_const.mul measurable_id)
  have hpoint (t : ℝ) : ‖(𝓕 φ) (δ * t) * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ) ≤
      ENNReal.ofReal A ^ (2 : ℝ) * (OAI.Analysis.Fourier.BochnerRiesz.timeDensity (δ * t) * ‖F t‖ₑ ^ (2 : ℝ)) := by
    let κ := OAI.Analysis.Fourier.BochnerRiesz.timeDensity (δ * t)
    let w := (1 + |δ * t|) ^ (-M)
    have hw : 0 ≤ w := Real.rpow_nonneg (by positivity) _
    have hcoeff : ‖(𝓕 φ) (δ * t)‖ₑ ≤ ENNReal.ofReal A * κ * ENNReal.ofReal w := by
      have h := ENNReal.ofReal_le_ofReal (hφ (δ * t))
      rw [ofReal_norm, ENNReal.ofReal_mul (mul_nonneg hA (by positivity)), ENNReal.ofReal_mul hA] at h
      exact h
    have hκ : κ ^ (2 : ℝ) ≤ κ := by
      rw [ENNReal.rpow_two, pow_two]
      simpa only [κ, mul_one] using mul_le_mul_right (OAI.Analysis.Fourier.BochnerRiesz.timeDensity_le_one (δ * t)) κ
    have hFsq : ‖F t‖ₑ ^ (2 : ℝ) = ENNReal.ofReal w ^ (2 : ℝ) *
        ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ) := by
      rw [show F t = w • OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x from rfl, enorm_smul,
        Real.enorm_eq_ofReal hw, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      _ = ‖(𝓕 φ) (δ * t)‖ₑ ^ (2 : ℝ) * ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ) := by
        rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ (ENNReal.ofReal A * κ * ENNReal.ofReal w) ^ (2 : ℝ) *
          ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ) :=
        mul_le_mul_left (ENNReal.rpow_le_rpow hcoeff (by norm_num)) _
      _ = ENNReal.ofReal A ^ (2 : ℝ) * (κ ^ (2 : ℝ) * (ENNReal.ofReal w ^ (2 : ℝ) *
          ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ))) := by
        simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
        ac_rfl
      _ ≤ ENNReal.ofReal A ^ (2 : ℝ) * (κ * (ENNReal.ofReal w ^ (2 : ℝ) *
          ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ ^ (2 : ℝ))) :=
        mul_le_mul_right (mul_le_mul_left hκ _) _
      _ = _ := by rw [hFsq]
  rw [thinShellSquareNorm_sq φ hδ f x, ENNReal.ofReal_mul hδ.le,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  have hi := lintegral_mono (μ := (volume : Measure ℝ)) hpoint
  have hconst : (∫⁻ t : ℝ, ENNReal.ofReal A ^ (2 : ℝ) *
      (OAI.Analysis.Fourier.BochnerRiesz.timeDensity (δ * t) * ‖F t‖ₑ ^ (2 : ℝ))) =
      ENNReal.ofReal A ^ (2 : ℝ) * ∫⁻ t : ℝ,
        OAI.Analysis.Fourier.BochnerRiesz.timeDensity (δ * t) * ‖F t‖ₑ ^ (2 : ℝ) :=
    lintegral_const_mul _ (hk.mul (hFm.enorm.pow_const (2 : ℝ)))
  rw [hconst] at hi
  simpa only [F, mul_assoc] using mul_le_mul_right hi (ENNReal.ofReal δ ^ (2 : ℝ))

end OAI.Analysis.Fourier.SquareFunction
