import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Wave
import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.Product
import OAI.Analysis.Fourier.WavePackets.Half.Wave.NormalizedKernel

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem norm_convolveKernel_le {n : ℕ} {K f : Space n → ℂ}
    (hK : Continuous K) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hKN : eLpNorm K 1 volume ≤ .ofReal B) (hf : ∀ x, ‖f x‖ ≤ M) (x : Space n) :
    ‖OAI.Analysis.Fourier.SquareFunction.convolveKernel K f x‖ ≤ B * M := by
  have H : ‖OAI.Analysis.Fourier.SquareFunction.convolveKernel K f x‖ₑ ≤ .ofReal (B * M) := by
    rw [OAI.Analysis.Fourier.SquareFunction.convolveKernel_commuted]
    calc
      _ ≤ ∫⁻ y, ‖f (x-y) • K y‖ₑ := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, .ofReal M * ‖K y‖ₑ := by
        apply lintegral_mono
        intro y
        dsimp only
        rw [enorm_smul]
        exact mul_le_mul' (by simpa only [← ofReal_norm] using ENNReal.ofReal_le_ofReal (hf (x-y))) le_rfl
      _ = .ofReal M * eLpNorm K 1 volume := by
        rw [lintegral_const_mul _ hK.enorm.measurable,
          eLpNorm_one_eq_lintegral_enorm hK.aestronglyMeasurable]
      _ ≤ .ofReal M * .ofReal B := mul_le_mul' le_rfl hKN
      _ = _ := by rw [← ENNReal.ofReal_mul hM, mul_comm]
  rw [← ofReal_norm] at H
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hB hM)).mp H

theorem frequencyWave_spacetime_young {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hf : Measurable f) (hi : Integrable f) {p : ℝ} (hp : 1 ≤ p) {A : ℝ≥0∞}
    (hK : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (waveKernel φ h t) 1 volume ≤ A) :
    eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1)
      (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ A * eLpNorm f (.ofReal p) volume := by
  apply observation_norm_le_of_slices (measurable_frequencyWave hφ hs hh hf hi) (by linarith)
  intro t ht
  exact (frequencyWave_slice_young hφ hs hh hf hi t (by
    simpa only [← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp)
    ENNReal.ofReal_ne_top).trans (mul_le_mul' (hK t ht) le_rfl)

theorem frequencyWave_ae_bounded {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hi : Integrable f) {M B : ℝ} (hM : 0 ≤ M) (hB : 0 ≤ B)
    (hK : ∀ t ∈ Icc (1 : ℝ) 2, eLpNorm (waveKernel φ h t) 1 volume ≤ .ofReal B)
    (hf : ∀ x, ‖f x‖ ≤ M) :
    ∀ᵐ z : Space n × ℝ ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n, ‖OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1‖ ≤ B * M := by
  filter_upwards [observation_ae_time (n := n)] with z hz
  rw [frequencyHalfWave_eq_convolveKernel hφ hs hh z.2 hi]
  exact norm_convolveKernel_le (continuous_waveKernel hφ hs h z.2) hM hB (hK z.2 hz) hf z.1

theorem uniform_waveKernel_L1 {n : ℕ} (hn : 0 < n) {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) (hz : 0 ∉ tsupport φ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 → ∀ t ∈ Icc (1 : ℝ) 2,
      eLpNorm (waveKernel φ h t) 1 volume ≤ .ofReal (C * h ^ (-((n:ℝ)-1)/2)) := by
  cases n with
  | zero => omega
  | succ d =>
    obtain ⟨C,hC,hb⟩ := OAI.Analysis.Fourier.WavePackets.uniform_semiclassicalWaveKernel_L1 hφ hs hz
    refine ⟨C,hC,?_⟩
    intro h hh h1 t ht
    simpa only [waveKernel, Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using! hb h hh h1 t ht

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
