import OAI.Analysis.Fourier.LocalSmoothing.Sharpness.FocusingLower
import OAI.Analysis.Fourier.WavePackets.Half.Wave.NormalizedKernel
import OAI.Analysis.Fourier.BochnerRiesz.TimeReversal

open OAI.Analysis.Fourier.Wave

noncomputable section
open _root_.MeasureTheory
open scoped ENNReal FourierTransform ComplexConjugate
namespace OAI.Analysis.Fourier.LocalSmoothing.Sharpness

theorem focusingWave_time_conj (n : ℕ) (N t : ℝ) (x : Space n) :
    focusingWave n N (-t) x = conj (focusingWave n N t (-x)) := by
  unfold focusingWave
  rw [← OAI.Analysis.Fourier.BochnerRiesz.angularInverse_conj]
  congr 1
  funext ξ
  simp [phase,radialSymbol,← Complex.exp_conj]

theorem eLpNorm_focusingWave_neg_time (n : ℕ) {N : ℝ} (hN : N ≠ 0)
    (t : ℝ) (p : ℝ≥0∞) :
    eLpNorm (focusingWave n N (-t)) p volume = eLpNorm (focusingWave n N t) p volume := by
  have hmap : Continuous (fun x : Space n => (x,t)) := continuous_id.prodMk continuous_const
  have hc := (continuous_focusingWave n (N := N) hN).comp hmap
  rw [funext (focusingWave_time_conj n N t)]
  calc
    _ = eLpNorm (fun x : Space n => focusingWave n N t (-x)) p volume :=
      eLpNorm_conj (fun x : Space n => focusingWave n N t (-x)) p volume
    _ = _ := eLpNorm_comp_measurePreserving hc.aestronglyMeasurable
      (Measure.measurePreserving_neg (volume : Measure (Space n)))

theorem focusingWave_eq_dilated_waveAmplitude {n : ℕ} {N : ℝ} (hN : 0 < N)
    (t : ℝ) :
    focusingWave n N t = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (fun ξ =>
      OAI.Analysis.Fourier.WavePackets.waveAmplitude (radialSymbol n) N⁻¹ t (N⁻¹•ξ)) := by
  funext x
  unfold focusingWave
  congr 1
  funext ξ
  unfold OAI.Analysis.Fourier.WavePackets.waveAmplitude phase
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hN)]
  have ht : (t / N⁻¹) * (N⁻¹*‖ξ‖) = t*‖ξ‖ := by field_simp
  rw [ht]
  congr 2
  push_cast
  ring

theorem focusingWave_initial_L1 {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N →
      eLpNorm (focusingWave n N (-(3/2))) 1 volume ≤
        ENNReal.ofReal (C*N^(radialOrder n)) := by
  cases n with
  | zero => omega
  | succ d =>
    obtain ⟨C,hC,hb⟩ := OAI.Analysis.Fourier.WavePackets.uniform_wave_annular_kernel
      (radialSymbol_contDiff (d+1)) (radialSymbol_hasCompactSupport (d+1))
      (radialSymbol_zero_notMem (d+1))
    refine ⟨C,hC,fun N hN => ?_⟩
    have hNp : 0 < N := lt_of_lt_of_le zero_lt_one hN
    have hNi : N⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hN
    have hi := OAI.Analysis.Fourier.WavePackets.waveAmplitude_integrable
      (radialSymbol_contDiff (d+1)).continuous (radialSymbol_hasCompactSupport (d+1)) N⁻¹ (3/2)
    rw [eLpNorm_focusingWave_neg_time (d+1) hNp.ne',focusingWave_eq_dilated_waveAmplitude hNp,
      OAI.Analysis.Fourier.BochnerRiesz.eLpNorm_angularInverse_dilate_one hi (inv_pos.mpr hNp),
      ← OAI.Analysis.Fourier.WavePackets.eLpNorm_fourierInv_eq_angularInverse hi]
    have h := hb N⁻¹ (inv_pos.mpr hNp) hNi (3/2) (by constructor <;> norm_num)
    have he : (N⁻¹)^(-(d:ℝ)/2) = N^(radialOrder (d+1)) := by
      rw [Real.inv_rpow hNp.le,← Real.rpow_neg hNp.le]
      congr 1
      simp only [radialOrder,Nat.cast_add,Nat.cast_one]
      ring
    simpa only [he] using h

theorem focusing_packet_initial_L1 {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 ≤ N → ∀ f : SchwartzMap (Space n) ℂ,
      (f : Space n → ℂ) = OAI.Analysis.Fourier.LocalSmoothing.angularInverse (focusingSymbol n N (3/2)) →
      eLpNorm f 1 volume ≤ ENNReal.ofReal (C*N^(radialOrder n)) := by
  obtain ⟨C,hC,hb⟩ := focusingWave_initial_L1 hn
  refine ⟨C,hC,fun N hN f hf => ?_⟩
  have he := funext (focusing_packet_initial hf)
  rw [he]
  exact hb N hN

end OAI.Analysis.Fourier.LocalSmoothing.Sharpness
