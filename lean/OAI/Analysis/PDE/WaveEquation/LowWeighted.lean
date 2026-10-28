import OAI.Analysis.PDE.WaveEquation.LowEstimate
import OAI.Analysis.PDE.WaveEquation.VelocitySymbol

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory
open scoped ENNReal ContDiff
noncomputable section
namespace OAI.Analysis.PDE.WaveEquation

open OAI.Analysis.Fourier.LocalSmoothing.Interpolation

theorem frequencyWavePrimitive_unweight {n : ℕ} (χ : Space n → ℂ)
    {m : Space n → ℝ} (hm : m.HasTemperateGrowth) (hne : ∀ ξ, m ξ ≠ 0)
    (f : SchwartzMap (Space n) ℂ) (t : ℝ) :
    frequencyWavePrimitive (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.unweightedCutoff χ m) t (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier m f) =
      frequencyWavePrimitive χ t f := by
  funext x
  unfold frequencyWavePrimitive
  simp only [OAI.Analysis.Fourier.LocalSmoothing.Interpolation.frequencyHalfWave_unweight χ hm hne]

theorem frequencyWavePrimitive_log_bound {n : ℕ} {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (s B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : SchwartzMap (Space n) ℂ, ∀ p : ℝ, 1 ≤ p →
      eLpNorm (fun z : Space n × ℝ ↦ frequencyWavePrimitive χ z.2 f z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B f) (ENNReal.ofReal p) volume := by
  let m : Space n → ℝ := fun ξ ↦
    (1+‖ξ‖^2)^(s/2) * Real.log (2+Real.sqrt (1+‖ξ‖^2))^B
  have hm : m.HasTemperateGrowth := OAI.Analysis.Fourier.BesselPotential.temperate_log_bessel_weight s B
  have hne (ξ : Space n) : m ξ ≠ 0 := by
    apply mul_ne_zero
    · exact (Real.rpow_pos_of_pos (by positivity) _).ne'
    · apply (Real.rpow_pos_of_pos _ B).ne'
      exact Real.log_pos (by linarith [Real.sqrt_nonneg (1+‖ξ‖^2)])
  obtain ⟨C,hC,hb⟩ := frequencyWavePrimitive_bound
    (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.contDiff_unweightedCutoff hχ hm hne) (OAI.Analysis.Fourier.LocalSmoothing.Interpolation.hasCompactSupport_unweightedCutoff m hc)
  refine ⟨C,hC,fun f p hp ↦ ?_⟩
  have H := hb (OAI.Analysis.Fourier.BesselPotential.angularSchwartzMultiplier m f) p hp
  simp only [frequencyWavePrimitive_unweight χ hm hne] at H
  change _ ≤ ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz s B f)
    (ENNReal.ofReal p) volume at H
  simpa only [OAI.Analysis.Fourier.BesselPotential.logBesselPotentialSchwartz_eq] using H

theorem contDiff_complex_velocityLowCutoff (n : ℕ) :
    ContDiff ℝ ∞ (fun ξ : Space n ↦ (velocityLowCutoff ξ : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (temperate_velocityLowCutoff n).1

theorem hasCompactSupport_complex_velocityLowCutoff (n : ℕ) :
    HasCompactSupport (fun ξ : Space n ↦ (velocityLowCutoff ξ : ℂ)) := by
  have h := (OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).hasCompactSupport.comp_smul (by norm_num : (2:ℝ)≠0)
  exact h.comp_left (g := Complex.ofReal) rfl

def waveLowVelocity {n : ℕ} (t : ℝ) (g : Space n → ℂ) (x : Space n) : ℂ :=
  frequencyWavePrimitive (fun ξ ↦ (velocityLowCutoff ξ : ℂ)) t g x

theorem logarithmicSobolev_lowVelocity {n : ℕ} (s B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : SchwartzMap (Space n) ℂ, ∀ p : ℝ, 1 ≤ p →
      eLpNorm (fun z : Space n × ℝ ↦ waveLowVelocity z.2 g z.1)
        (ENNReal.ofReal p) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal C * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential s B g) (ENNReal.ofReal p) volume :=
  frequencyWavePrimitive_log_bound (contDiff_complex_velocityLowCutoff n)
    (hasCompactSupport_complex_velocityLowCutoff n) s B

end OAI.Analysis.PDE.WaveEquation
