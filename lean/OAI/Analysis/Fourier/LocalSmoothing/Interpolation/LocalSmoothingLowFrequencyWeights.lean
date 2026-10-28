import OAI.Analysis.Fourier.LocalSmoothing.Interpolation.LocalSmoothingLowFrequencyCore
import OAI.Analysis.Fourier.LocalSmoothing.DyadicCutoff

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem fixedFrequency_weighted_bound_of_kernel {n : ℕ} {p : ℝ} (hp : 1 ≤ p)
    {χ : Space n → ℂ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    {m : Space n → ℝ} (hm : m.HasTemperateGrowth) (hne : ∀ ξ, m ξ ≠ 0)
    (hkernel : ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (1 : ℝ) 2,
      eLpNorm (waveKernel (unweightedCutoff χ m) 1 t) 1 volume ≤ .ofReal C) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave χ 1 z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤ .ofReal C *
          eLpNorm (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier m f) (.ofReal p) volume := by
  have hd := contDiff_unweightedCutoff hχ hm hne
  have hs := hasCompactSupport_unweightedCutoff m hc
  obtain ⟨C,hC,hkernel⟩ := hkernel
  refine ⟨C,hC,?_⟩
  intro f
  have H := frequencyWave_spacetime_young hd.continuous hs (by norm_num : (0:ℝ)<1)
    (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier m f).continuous.measurable
    (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier m f).integrable hp hkernel
  simpa only [frequencyHalfWave_unweight χ hm hne f] using H

theorem lowFrequency_bessel_bound_of_kernel {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (σ : ℝ)
    (hkernel : ∀ χ : Space n → ℂ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (1 : ℝ) 2,
        eLpNorm (waveKernel χ 1 t) 1 volume ≤ .ofReal C) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff 1 z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.besselPotential σ f) (.ofReal p) volume := by
  have hm := Function.hasTemperateGrowth_one_add_norm_sq_rpow (Space n) (σ/2)
  have hne (ξ : Space n) : (1+‖ξ‖^2)^(σ/2) ≠ 0 :=
    (Real.rpow_pos_of_pos (by positivity) _).ne'
  have hχ := OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff n
  have hc := OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingLowCutoff n
  obtain ⟨C,hC,hb⟩ := fixedFrequency_weighted_bound_of_kernel hp hχ hc hm hne
    (hkernel _ (contDiff_unweightedCutoff hχ hm hne) (hasCompactSupport_unweightedCutoff _ hc))
  refine ⟨C,hC,?_⟩
  intro f
  have H := hb f
  change _ ≤ .ofReal C * eLpNorm (OAI.Analysis.Fourier.BesselPotential.besselPotentialSchwartz σ f) (.ofReal p) volume at H
  simpa only [OAI.Analysis.Fourier.BesselPotential.besselPotentialSchwartz_eq] using H

theorem lowFrequency_logBessel_bound_of_kernel {n : ℕ} {p : ℝ} (hp : 1 ≤ p) (s B : ℝ)
    (hkernel : ∀ χ : Space n → ℂ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc (1 : ℝ) 2,
        eLpNorm (waveKernel χ 1 t) 1 volume ≤ .ofReal C) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.frequencyHalfWave OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff 1 z.2 f z.1)
        (.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      .ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) (.ofReal p) volume := by
  have hm := OAI.Analysis.Fourier.BesselPotential.temperate_log_bessel_weight (H := Space n) s B
  have hne (ξ : Space n) : (1+‖ξ‖^2)^(s/2) *
      Real.log (2+Real.sqrt (1+‖ξ‖^2))^B ≠ 0 := by
    apply mul_ne_zero
    · exact (Real.rpow_pos_of_pos (by positivity) _).ne'
    · apply (Real.rpow_pos_of_pos _ B).ne'
      exact Real.log_pos (by linarith [Real.sqrt_nonneg (1+‖ξ‖^2)])
  have hχ := OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingLowCutoff n
  have hc := OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingLowCutoff n
  obtain ⟨C,hC,hb⟩ := fixedFrequency_weighted_bound_of_kernel hp hχ hc hm hne
    (hkernel _ (contDiff_unweightedCutoff hχ hm hne) (hasCompactSupport_unweightedCutoff _ hc))
  refine ⟨C,hC,?_⟩
  intro f
  have H := hb f
  change _ ≤ .ofReal C * eLpNorm (OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz s B f) (.ofReal p) volume at H
  simpa only [OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz_eq] using H

end OAI.Analysis.Fourier.LocalSmoothing.Interpolation
