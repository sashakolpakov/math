import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.CriticalMoment
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.NormFromMoment

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped ENNReal

def inputExponent (n : ℕ) (p : ℝ) : ℝ := (n:ℝ)-radialOrder n-1/p

theorem frequencyMomentExponent_div {n : ℕ} {p : ℝ} (hp : p ≠ 0) :
    frequencyMomentExponent n p / p = inputExponent n p := by
  unfold frequencyMomentExponent inputExponent
  field_simp

theorem focusing_packet_critical_norm_lower {n : ℕ} (hn : 2 ≤ n) :
    ∃ c A : ℝ, 0 < c ∧ 1 ≤ A ∧ ∀ N : ℝ, 4*A ≤ N →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N (3/2) ξ) →
      ENNReal.ofReal (c*N^(inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))*
        (Real.log (N/(4*A)))^(1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) ≤
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
  obtain ⟨c,A,hc,hA,h⟩ := focusing_packet_critical_moment_lower hn
  have hp := criticalExponent_pos hn
  refine ⟨c^(1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n),A,by positivity,hA,fun N hN f hf => ?_⟩
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hN0 : 0 < N := (by positivity : 0 < 4*A).trans_le hN
  have hlog : 0 ≤ Real.log (N/(4*A)) :=
    Real.log_nonneg ((le_div_iff₀ (by positivity : 0 < 4*A)).2 (by simpa using hN))
  have hl := norm_lower_of_moment (OAI.Analysis.Fourier.LocalSmoothing.continuous_halfWaveIntegral f).aestronglyMeasurable hp
    (by positivity : 0 ≤ c*N^(frequencyMomentExponent n (criticalExponent n))*Real.log (N/(4*A)))
    (h N hN f hf)
  rw [moment_root_factor hc.le hN0 hlog,frequencyMomentExponent_div hp.ne'] at hl
  exact hl

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
