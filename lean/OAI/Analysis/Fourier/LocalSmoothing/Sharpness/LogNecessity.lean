import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.CriticalNorm
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.LogPowers
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.PacketInputBound
import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.AnnularWeights

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

open Set Filter _root_.MeasureTheory OAI.Analysis.Fourier.LocalSmoothing.Sharpness
open scoped ENNReal

/-- The logarithmic obstruction in Proposition `prop:sharpness`, for the
actual logarithmic Bessel potential and actual half-wave. -/
theorem logarithmic_estimate_exponent_necessary_of_input_bound {n : ℕ} (hn : 2 ≤ n)
    (hinputBound : PacketInputBound n) {β : ℝ}
    (hbound : ∃ K : ℝ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal K * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential 0 β f)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume) :
    1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n ≤ β := by
  obtain ⟨K,hK⟩ := hbound
  obtain ⟨c,A,hc,hA,hlo⟩ := focusing_packet_critical_norm_lower hn
  obtain ⟨D,hD,hinput⟩ := hinputBound
  obtain ⟨W,hW,hweight⟩ := sharpness_annular_log_bessel_bound n 0 β
  have hn' : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := criticalExponent_pos hn
  have hp1 : 1 ≤ OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n := by
    unfold OAI.Analysis.Fourier.LocalSmoothing.criticalExponent
    apply (le_div_iff₀ (by linarith : 0 < (n:ℝ)-1)).2
    linarith
  have hK0 : 0 ≤ max K 0 := le_max_right _ _
  apply shifted_log_power_necessary hc (show 0 ≤ (max K 0)*W*D by positivity)
    (one_div_pos.mpr hp) (show 0 < 4*A by nlinarith)
  filter_upwards [eventually_ge_atTop (max 4 (4*A))] with N hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hNA : 4*A ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  obtain ⟨f,hf,hfF⟩ := exists_focusing_packet n hN0.ne' (3/2)
  have hinput' := hinput (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n) hp1 N (by linarith) f hf
  have hweight' := hweight N hN4 f (focusing_packet_annular hN0 hfF)
    (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))
    (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1)
    ENNReal.ofReal_ne_top
  simp only [Real.rpow_zero,mul_one] at hweight'
  have hlog : 0 ≤ 1+Real.log (N/4) := by
    have := Real.log_nonneg (show 1 ≤ N/4 by linarith)
    linarith
  have he : ENNReal.ofReal (c*N^(inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))*
      (Real.log (N/(4*A)))^(1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) ≤
      ENNReal.ofReal (((max K 0)*W*D)*N^(inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))*
        (1+Real.log (N/4))^β) := by
    calc
      _ ≤ _ := hlo N hNA f hfF
      _ ≤ ENNReal.ofReal (max K 0) * eLpNorm (OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential 0 β f)
          (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume :=
        (hK f).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl)
      _ ≤ ENNReal.ofReal (max K 0) * (ENNReal.ofReal (W*(1+Real.log (N/4))^β) *
          ENNReal.ofReal (D*N^(inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)))) :=
        mul_le_mul' le_rfl (hweight'.trans (mul_le_mul' le_rfl hinput'))
      _ = _ := by
        rw [←ENNReal.ofReal_mul (mul_nonneg hW (Real.rpow_nonneg hlog _)),
          ←ENNReal.ofReal_mul hK0]
        congr 1
        ring
  have hr := (ENNReal.ofReal_le_ofReal_iff (show 0 ≤
      ((max K 0)*W*D)*N^(inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n))*(1+Real.log (N/4))^β
      by positivity)).mp he
  have hnPow : 0 < N^(inputExponent n (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) := by positivity
  apply (mul_le_mul_iff_of_pos_right hnPow).mp
  convert hr using 1 <;> ring

theorem logBesselPotential_zero_zero {n : ℕ} (f : SchwartzMap (Space n) ℂ) :
    OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential 0 0 f = f := by
  funext x
  simp only [OAI.Analysis.Fourier.LocalSmoothing.logBesselPotential,zero_div,Real.rpow_zero,mul_one,one_smul]
  exact OAI.Analysis.Fourier.Restriction.angularInverse_angularFourier_schwartz f x

theorem critical_lossless_estimate_false_of_input_bound {n : ℕ} (hn : 2 ≤ n)
    (hinputBound : PacketInputBound n) :
    ¬ ∃ K : ℝ, ∀ f : SchwartzMap (Space n) ℂ,
      eLpNorm (fun z : Space n × ℝ => OAI.Analysis.Fourier.LocalSmoothing.halfWaveIntegral z.2 f z.1)
        (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) (OAI.Analysis.Fourier.LocalSmoothing.observationMeasure n) ≤
      ENNReal.ofReal K * eLpNorm f (ENNReal.ofReal (OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n)) volume := by
  intro h
  have hb : 1/OAI.Analysis.Fourier.LocalSmoothing.criticalExponent n ≤ 0 := logarithmic_estimate_exponent_necessary_of_input_bound hn hinputBound
    (by simpa only [logBesselPotential_zero_zero] using h)
  exact (one_div_pos.mpr (criticalExponent_pos hn)).not_ge hb

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
