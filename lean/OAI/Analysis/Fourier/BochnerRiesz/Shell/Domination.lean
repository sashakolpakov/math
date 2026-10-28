import OAI.Analysis.Fourier.BochnerRiesz.Shell.Formula
import OAI.Analysis.Fourier.BochnerRiesz.TimeDecay

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory FourierTransform
open scoped ENNReal

noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem schwartz_time_decay_enorm (φ : SchwartzMap ℝ ℂ) (M : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ,
      ‖φ t‖ₑ ≤ ENNReal.ofReal A * timeDensity t * ENNReal.ofReal ((1 + |t|) ^ (-M)) := by
  obtain ⟨A, hA, hb⟩ := schwartz_time_decay φ M
  refine ⟨A, hA, ?_⟩
  intro t
  rw [← ofReal_norm]
  calc
    _ ≤ ENNReal.ofReal (A * (1 + |t|) ^ (-2 : ℝ) * (1 + |t|) ^ (-M)) :=
      ENNReal.ofReal_le_ofReal (hb t)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hA.le]
      rfl

theorem measurable_weightedTime_slice {n : ℕ} (f : SchwartzMap (Space n) ℂ) (M : ℝ)
    (x : Space n) : Measurable (fun t : ℝ ↦
      weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) (x, t)) := by
  have hc := continuous_weightedTimeFunction M (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral (n := n) f)
  have hg : Continuous (fun t : ℝ ↦ (x, t)) := continuous_const.prodMk continuous_id
  have H := hc.comp hg
  simpa only [Function.comp_def] using H.measurable

theorem enorm_thinShellCycles_le_time {n : ℕ} (φ : SchwartzMap ℝ ℂ)
    (f : SchwartzMap (Space n) ℂ) (s : ℝ) (x : Space n) :
    ‖OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s‖ₑ ≤
      ∫⁻ t : ℝ, ‖(𝓕 φ : SchwartzMap ℝ ℂ) t‖ₑ * ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ := by
  rw [thinShellCycles_eq_wave_integral φ zero_lt_one f x s]
  simp only [Complex.ofReal_one, one_mul]
  calc
    _ ≤ ∫⁻ t : ℝ, ‖Complex.exp ((2 * Real.pi * t * s : ℝ) * Complex.I) *
        ((𝓕 φ : SchwartzMap ℝ ℂ) t * OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x)‖ₑ := enorm_integral_le_lintegral_enorm _
    _ = _ := by
      apply lintegral_congr
      intro t
      have he : ‖Complex.exp ((2 * Real.pi * t * s : ℝ) * Complex.I)‖ₑ = 1 := by
        rw [← ofReal_norm]
        simp [Complex.norm_exp]
      rw [enorm_mul, he, one_mul, enorm_mul]

theorem enorm_weightedTimeFunction {n : ℕ} (M : ℝ) (F : Space n × ℝ → ℂ)
    (x : Space n) (t : ℝ) :
    ‖weightedTimeFunction M F (x, t)‖ₑ =
      ENNReal.ofReal ((1 + |t|) ^ (-M)) * ‖F (x, t)‖ₑ := by
  have hw : 0 ≤ (1 + |t|) ^ (-M) := Real.rpow_nonneg (by positivity) _
  simp only [weightedTimeFunction, enorm_smul, Real.enorm_eq_ofReal hw]

theorem thinShellCycles_weighted_domination (φ : SchwartzMap ℝ ℂ) (M : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (f : SchwartzMap (Space n) ℂ) (s : ℝ) (x : Space n),
      ‖OAI.Analysis.Fourier.SquareFunction.thinShellCycles φ 1 f x s‖ₑ ≤ ENNReal.ofReal A *
        ∫⁻ t : ℝ, timeDensity t *
          ‖weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) (x, t)‖ₑ := by
  obtain ⟨A, hA, hb⟩ := schwartz_time_decay_enorm (𝓕 φ : SchwartzMap ℝ ℂ) M
  refine ⟨A, hA, ?_⟩
  intro n f s x
  calc
    _ ≤ ∫⁻ t : ℝ, ‖(𝓕 φ : SchwartzMap ℝ ℂ) t‖ₑ * ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ :=
      enorm_thinShellCycles_le_time φ f s x
    _ ≤ ∫⁻ t : ℝ, ENNReal.ofReal A * (timeDensity t *
        ‖weightedTimeFunction M (fun z : Space n × ℝ ↦ OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1) (x, t)‖ₑ) := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [enorm_weightedTimeFunction]
      simpa only [mul_assoc] using mul_le_mul' (hb t) (le_refl ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t f x‖ₑ)
    _ = _ := by
      apply lintegral_const_mul''
      apply measurable_timeDensity.aemeasurable.mul
      exact (measurable_weightedTime_slice f M x).enorm.aemeasurable

end OAI.Analysis.Fourier.BochnerRiesz
