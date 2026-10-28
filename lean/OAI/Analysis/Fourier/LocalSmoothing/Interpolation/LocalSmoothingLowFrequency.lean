import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.LocalSmoothingLowFrequencyWeights
import OAI.Analysis.Fourier.WavePackets.Half.Wave.LowKernel
import OAI.Analysis.Fourier.LocalSmoothing.DyadicCutoff

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem uniform_fixed_waveKernel_L1 {n : ℕ} (hn : 0 < n) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (1 : ℝ) 2,
      eLpNorm (waveKernel χ 1 t) 1 volume ≤ .ofReal C := by
  cases n with
  | zero => omega
  | succ d =>
    obtain ⟨C,hC,hb⟩ := OAI.Analysis.Fourier.WavePackets.uniform_fixed_semiclassicalWaveKernel_L1 hχ hc
    refine ⟨C,hC,?_⟩
    intro t ht
    simpa only [waveKernel] using! hb t ht

/-- A fixed smooth multiplier admits any nonvanishing temperate input
weight. The inverse weight is included in the actual compact kernel. -/
theorem fixedFrequency_weighted_bound {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p)
    {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {m : Space n → ℝ} (hm : m.HasTemperateGrowth) (hne : ∀ ξ, m ξ ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ .ofReal C *
          eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier m f) (.ofReal p) volume := by
  exact fixedFrequency_weighted_bound_of_kernel hp hχ hc hm hne
    (uniform_fixed_waveKernel_L1 hn (contDiff_unweightedCutoff hχ hm hne)
      (hasCompactSupport_unweightedCutoff m hc))

theorem lowFrequency_bessel_bound {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) (σ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff 1 z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f) (.ofReal p) volume := by
  exact lowFrequency_bessel_bound_of_kernel hp σ
    (fun _ hχ hc => uniform_fixed_waveKernel_L1 hn hχ hc)

theorem lowFrequency_logBessel_bound {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 1 ≤ p) (s B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff 1 z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) (.ofReal p) volume := by
  exact lowFrequency_logBessel_bound_of_kernel hp s B
    (fun _ hχ hc => uniform_fixed_waveKernel_L1 hn hχ hc)

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
