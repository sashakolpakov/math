import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.MomentLower
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.LogIntegral

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped ENNReal

theorem criticalExponent_pos {n : ℕ} (hn : 2 ≤ n) : 0 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  exact div_pos (by positivity) (by linarith)

theorem timeMomentExponent_critical {n : ℕ} (hn : 2 ≤ n) :
    timeMomentExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) = -1 := by
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hne : (n:ℝ)-1 ≠ 0 := by linarith
  unfold timeMomentExponent radialOrder OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
  rw [Nat.cast_sub (by omega : 1 ≤ n),Nat.cast_one]
  field_simp
  ring

/-- The actual focusing packet has the critical logarithmic lower moment.
The logarithm is obtained by integrating its outgoing shell, not postulated. -/
theorem focusing_packet_critical_moment_lower {n : ℕ} (hn : 2 ≤ n) :
    ∃ c A : ℝ, 0 < c ∧ 1 ≤ A ∧ ∀ N : ℝ, 4*A ≤ N →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N (3/2) ξ) →
      ENNReal.ofReal (c*N^(frequencyMomentExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))*
        Real.log (N/(4*A))) ≤
      ∫⁻ z, ‖OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1‖ₑ^(OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) ∂OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n := by
  obtain ⟨A,hA,h⟩ := focusing_packet_integrated_moment_lower (show 1 ≤ n by omega)
  obtain ⟨c,hc,h⟩ := h (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) (criticalExponent_pos hn).le
  refine ⟨c,A,hc,hA,fun N hN f hf => ?_⟩
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hN0 : 0 < N := (by positivity : 0 < 4*A).trans_le hN
  have hl := h N hN0 f hf
  simp only [timeMomentExponent_critical hn,Real.rpow_neg_one] at hl
  rw [lintegral_inv_focusing_interval hA0 hN,
    ←ENNReal.ofReal_mul (by positivity)] at hl
  exact hl

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
