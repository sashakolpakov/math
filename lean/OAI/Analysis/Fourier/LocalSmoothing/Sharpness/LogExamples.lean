import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.CriticalNorm
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.LogPowers
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.PacketInputBound
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.PacketNonzero

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory
open scoped ENNReal

theorem focusing_packet_critical_norm_log_lower {n : ℕ} (hn : 2 ≤ n) :
    ∃ c N₀ : ℝ, 0 < c ∧ 4 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ f : SchwartzMap (Space n) ℂ,
      (∀ ξ, OAI.Analysis.Fourier.LocalSmoothing.angularFourier f ξ = focusingSymbol n N (3/2) ξ) →
      ENNReal.ofReal (c*N^(inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))*
        (Real.log N)^(1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) ≤
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) := by
  obtain ⟨c,A,hc,hA,h⟩ := focusing_packet_critical_norm_lower hn
  have hp : 0 < 1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := one_div_pos.mpr (criticalExponent_pos hn)
  refine ⟨c*(1/2:ℝ)^(1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n),(4*A)^2,by positivity,by nlinarith,
    fun N hN f hf => ?_⟩
  have hNA : 4*A ≤ N := by nlinarith [sq_nonneg (4*A-1)]
  have hN1 : 1 ≤ N := by nlinarith
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hlo := log_quotient_ge_half (show 1 ≤ 4*A by linarith) hN
  have hr := Real.rpow_le_rpow (mul_nonneg (by norm_num) hlog) hlo hp.le
  have hm := mul_le_mul_of_nonneg_left hr
    (mul_nonneg hc.le (Real.rpow_nonneg hN0.le (inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))))
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 1/2) hlog] at hm
  have hb := ENNReal.ofReal_le_ofReal hm
  apply le_trans ?_ (h N hNA f hf)
  convert hb using 1 ; congr 1 ; ring

/-- Explicit nonzero annular Schwartz examples realize the logarithmic
lower bound in Proposition `prop:sharpness`. -/
theorem critical_logarithmic_examples_of_input_bound {n : ℕ} (hn : 2 ≤ n)
    (hinputBound : PacketInputBound n) :
    ∃ c N₀ : ℝ, 0 < c ∧ 4 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∃ f : SchwartzMap (Space n) ℂ, f ≠ 0 ∧
      (tsupport (OAI.Analysis.Fourier.LocalSmoothing.angularFourier f) ⊆ {ξ | N ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2*N}) ∧
      ENNReal.ofReal (c*(Real.log N)^(1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) ≤
        eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
          (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) /
        eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  obtain ⟨c,N₀,hc,hN₀,hlo⟩ := focusing_packet_critical_norm_log_lower hn
  obtain ⟨D,hD,hinput⟩ := hinputBound
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := criticalExponent_pos hn
  have hp1 : 1 ≤ OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := by
    unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
    apply (le_div_iff₀ (by linarith : 0 < (n:ℝ)-1)).2
    linarith
  refine ⟨c/D,N₀,div_pos hc hD,hN₀,fun N hN => ?_⟩
  have hN2 : 2 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  obtain ⟨f,hf,hfF⟩ := exists_focusing_packet n hN0.ne' (3/2)
  have hfne := focusing_packet_ne_zero (show 1 ≤ n by omega) hN0 hfF
  refine ⟨f,hfne,focusing_packet_tsupport hN0 hfF,?_⟩
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl (schwartz_eLpNorm_ne_zero hfne (ENNReal.ofReal_pos.mpr hp).ne'))
    (Or.inl (f.memLp _ volume).ne)).mpr
  calc
    _ ≤ ENNReal.ofReal (c/D*(Real.log N)^(1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) *
        ENNReal.ofReal (D*N^(inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))) :=
      mul_le_mul' le_rfl (hinput (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) hp1 N hN2 f hf)
    _ = ENNReal.ofReal (c*N^(inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))*
        (Real.log N)^(1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) := by
      rw [←ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ ≤ _ := hlo N hN f hfF

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
