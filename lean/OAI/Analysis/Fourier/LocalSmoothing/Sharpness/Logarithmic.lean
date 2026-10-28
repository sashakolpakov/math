import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.LogExamples
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.LogNecessity
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.InputLp

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory
open scoped ENNReal

namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

/-- The explicit annular counterexamples in Proposition `prop:sharpness`.
All estimates, including the input norm, are derived for the constructed
Schwartz packet. -/
theorem critical_logarithmic_examples {n : ℕ} (hn : 2 ≤ n) :
    ∃ c N₀ : ℝ, 0 < c ∧ 4 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∃ f : SchwartzMap (Space n) ℂ, f ≠ 0 ∧
      (tsupport (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) ⊆ {ξ | N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2*N}) ∧
      ENNReal.ofReal (c*(Real.log N)^(1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) ≤
        eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
          (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) /
        eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume :=
  critical_logarithmic_examples_of_input_bound hn (focusing_packet_initial_Lp (by omega))

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

theorem logarithmic_estimate_exponent_necessary {n : ℕ} (hn : 2 ≤ n) {β : ℝ}
    (hbound : ∃ K : ℝ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal K * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential 0 β f)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume) :
    1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n ≤ β :=
  logarithmic_estimate_exponent_necessary_of_input_bound hn
    (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.focusing_packet_initial_Lp (by omega)) hbound

theorem critical_lossless_estimate_false {n : ℕ} (hn : 2 ≤ n) :
    ¬ ∃ K : ℝ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume :=
  critical_lossless_estimate_false_of_input_bound hn
    (OAI.Analysis.Fourier.LocalSmoothing.Sharpness.focusing_packet_initial_Lp (by omega))

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
