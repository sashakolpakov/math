import OAI.Analysis.Fourier.LocalSmoothing.L2
import OAI.Analysis.Fourier.BochnerRiesz.Projection
import OAI.Analysis.Fourier.WavePackets.Assembly
import OAI.Analysis.Fourier.SquareFunction.VectorYoung

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

open OAI.Analysis.Fourier.WavePackets

def waveKernel {n : ℕ} (φ : Space n → ℂ) (h t : ℝ) (x : Space n) : ℂ :=
  (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹ * OAI.Analysis.Fourier.WavePackets.semiclassicalWaveKernel volume φ h t x

theorem continuous_waveKernel {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) (h t : ℝ) :
    Continuous (waveKernel φ h t) := by
  have hc : Continuous (fun z : ℝ × Space n => OAI.Analysis.Fourier.WavePackets.semiclassicalWaveKernel volume φ h z.1 z.2) :=
    OAI.Analysis.Fourier.WavePackets.continuous_semiclassicalWaveKernel_spacetime (E := Space n) (μ := volume) hφ hs h
  have ht : Continuous (fun x : Space n => (t,x)) := continuous_const.prodMk continuous_id
  simpa only [waveKernel, Function.comp_def] using!
    (hc.comp ht).const_mul ((((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹)

theorem frequencyHalfWave_eq_convolveKernel {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (t : ℝ) {f : Space n → ℂ} (hf : Integrable f) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t f = OAI.Analysis.Fourier.SquareFunction.convolveKernel (waveKernel φ h t) f := by
  funext x
  rw [(OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hf x).2]
  unfold OAI.Analysis.Fourier.SquareFunction.convolveKernel waveKernel
  simp_rw [smul_eq_mul, ← mul_assoc, mul_comm (f _) (((2 * Real.pi : ℝ) : ℂ) ^ n)⁻¹,
    mul_assoc, mul_comm (f _) (OAI.Analysis.Fourier.WavePackets.semiclassicalWaveKernel _ _ _ _ _)]
  rw [integral_const_mul]

theorem frequencyHalfWave_add {n : ℕ} {φ : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (t : ℝ) {f g : Space n → ℂ} (hf : Integrable f) (hg : Integrable g) (x : Space n) :
    OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t (fun y => f y + g y) x =
      OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t f x + OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t g x := by
  change OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t (f + g) x = _
  rw [(OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t (hf.add hg) x).2,
    (OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hf x).2,
    (OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hg x).2]
  simp_rw [Pi.add_apply, mul_add]
  rw [integral_add (OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hf x).1
    (OAI.Analysis.Fourier.WavePackets.frequencyHalfWave_eq_integral_kernel hφ hs hh t hg x).1, mul_add]

theorem measurable_frequencyWave {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hf : Measurable f) (hi : Integrable f) :
    Measurable (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) := by
  have H : Measurable (fun z : ℝ × Space n => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.1 f z.2) :=
    OAI.Analysis.Fourier.WavePackets.measurable_frequencyHalfWave_spacetime (n := n) hφ hs hh hf hi
  simpa only [Function.comp_def, Prod.swap] using
    H.comp (show Measurable (Prod.swap : Space n × ℝ → ℝ × Space n) from measurable_swap)

theorem halfWave_annularProject {n : ℕ} {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (f : SchwartzMap (Space n) ℂ) (t : ℝ) :
    OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral t (OAI.Analysis.Fourier.BochnerRiesz.annularProject φ h f) = OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t f := by
  unfold OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave
  congr 1
  funext ξ
  rw [OAI.Analysis.Fourier.BochnerRiesz.angularFourier_annularProject hφ hs hh]
  exact (mul_assoc _ _ _).symm

theorem frequencyWave_two {n : ℕ} {φ : Space n → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hs : HasCompactSupport φ) :
    ∃ A : ℝ, 0 < A ∧ ∀ h : ℝ, 0 < h → ∀ f : SchwartzMap (Space n) ℂ,
      MemLp (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) 2
        (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ∧
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) 2
        (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ .ofReal A * eLpNorm f 2 volume := by
  obtain ⟨A,hA,hbound⟩ := OAI.Analysis.Fourier.BochnerRiesz.annularProject_uniform_bound hφ hs
  refine ⟨A,hA,?_⟩
  intro h hh f
  have he : (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h z.2 f z.1) =
      fun z => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 (OAI.Analysis.Fourier.BochnerRiesz.annularProject φ h f) z.1 := by
    funext z
    exact congrFun (halfWave_annularProject hφ hs hh f z.2).symm z.1
  rw [he]
  refine ⟨OAI.Analysis.Fourier.LocalSmoothing.memLp_halfWaveIntegral_spacetime_two _, ?_⟩
  rw [OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral_spacetime_eLpNorm_two]
  exact hbound h hh f 2 (by norm_num) (by norm_num)

theorem frequencyWave_slice_young {n : ℕ} {φ f : Space n → ℂ}
    (hφ : Continuous φ) (hs : HasCompactSupport φ) {h : ℝ} (hh : 0 < h)
    (hf : Measurable f) (hi : Integrable f) (t : ℝ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave φ h t f) p volume ≤
      eLpNorm (waveKernel φ h t) 1 volume * eLpNorm f p volume := by
  rw [frequencyHalfWave_eq_convolveKernel hφ hs hh t hi]
  exact OAI.Analysis.Fourier.SquareFunction.eLpNorm_convolveKernel_le (continuous_waveKernel hφ hs h t) hf hp hpt

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
