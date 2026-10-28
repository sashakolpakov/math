import OAI.Analysis.Fourier.WavePackets.Half.Wave.LowAnnulus
import OAI.Analysis.Fourier.LocalSmoothing.DyadicCutoff
import OAI.Analysis.Fourier.LocalSmoothing.DyadicReconstruction

open OAI.Analysis.Fourier.Wave

noncomputable section
namespace OAI.Analysis.Fourier.WavePackets

open Set Filter _root_.MeasureTheory
open scoped ContDiff Topology FourierTransform ENNReal

def inwardAnnulus {n : ℕ} (ξ : Space n) : ℂ := OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff ((2:ℝ) • ξ)

theorem inwardAnnulus_eq {n : ℕ} (ξ : Space n) :
    inwardAnnulus ξ = OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ξ-OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ((2:ℝ) • ξ) := by
  simp [inwardAnnulus,OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff,smul_smul]

theorem contDiff_inwardAnnulus (n : ℕ) : ContDiff ℝ ∞ (@inwardAnnulus n) :=
  (OAI.Analysis.Fourier.LocalSmoothing.contDiff_smoothingAnnularCutoff n).comp (contDiff_id.const_smul _)

theorem hasCompactSupport_inwardAnnulus (n : ℕ) : HasCompactSupport (@inwardAnnulus n) :=
  (OAI.Analysis.Fourier.LocalSmoothing.hasCompactSupport_smoothingAnnularCutoff n).comp_smul (by norm_num)

theorem zero_notMem_tsupport_inwardAnnulus (n : ℕ) :
    (0 : Space n) ∉ tsupport inwardAnnulus := by
  rw [notMem_tsupport_iff_eventuallyEq]
  filter_upwards [Metric.ball_mem_nhds (0 : Space n) (by norm_num : (0:ℝ)<1/2)] with ξ hξ
  have hn : ‖ξ‖ < 1/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hξ
  change OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff ((2:ℝ) • ξ) = 0
  apply OAI.Analysis.Fourier.LocalSmoothing.smoothingAnnularCutoff_eq_zero
  rw [norm_smul]
  norm_num only [Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
  linarith

def lowRemainder {n : ℕ} (χ : Space n → ℂ) (T : ℝ) (ξ : Space n) : ℂ :=
  χ ξ * (Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ))-1) * OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ξ

theorem lowWaveAnnulus_sum {n : ℕ} (χ : Space n → ℂ) (T : ℝ) (N : ℕ) (ξ : Space n) :
    ∑ k ∈ Finset.range N, lowWaveAnnulus inwardAnnulus χ (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale k) T ξ =
      χ ξ * (Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ))-1) *
        (OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ξ-OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ((2:ℝ)^N • ξ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ,ih]
      simp only [lowWaveAnnulus,inwardAnnulus_eq,OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale,inv_pow,inv_inv,
        smul_smul,pow_succ]
      ring_nf

theorem eventually_smoothingLowCutoff_inward_zero {n : ℕ} {ξ : Space n} (hξ : ξ ≠ 0) :
    ∀ᶠ N : ℕ in atTop, OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ((2:ℝ)^N • ξ) = 0 := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  have hg : Tendsto (fun N : ℕ => (2:ℝ)^N*‖ξ‖) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)).atTop_mul_const hn
  filter_upwards [hg.eventually (eventually_ge_atTop (16:ℝ))] with N hN
  unfold OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff
  rw [(OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump n).zero_of_le_dist]
  · simp
  · simpa only [OAI.Analysis.Fourier.LocalSmoothing.smoothingLowBump,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) N)] using hN

theorem tendsto_lowWaveAnnulus_sum {n : ℕ} (χ : Space n → ℂ) (T : ℝ) (ξ : Space n) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N,
      lowWaveAnnulus inwardAnnulus χ (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale k) T ξ)
      atTop (𝓝 (lowRemainder χ T ξ)) := by
  simp only [lowWaveAnnulus_sum]
  by_cases hξ : ξ = 0
  · subst ξ
    simp [lowRemainder]
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_smoothingLowCutoff_inward_zero hξ] with N hN
    simp only [lowRemainder,hN,sub_zero]

theorem norm_lowWaveAnnulus_sum_le {n : ℕ} (χ : Space n → ℂ) (T : ℝ) (N : ℕ) (ξ : Space n) :
    ‖∑ k ∈ Finset.range N,lowWaveAnnulus inwardAnnulus χ (OAI.Analysis.Fourier.LocalSmoothing.smoothingDyadicScale k) T ξ‖ ≤
      4*‖χ ξ‖ := by
  rw [lowWaveAnnulus_sum,norm_mul,norm_mul]
  have he : ‖Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ))-1‖ ≤ 2 := by
    have H := norm_sub_le (Complex.exp (-Complex.I * (T*‖ξ‖ : ℝ))) (1:ℂ)
    norm_num [Complex.norm_exp] at H
    simpa only [Complex.ofReal_mul,neg_mul] using H
  have hl : ‖OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ξ-OAI.Analysis.Fourier.LocalSmoothing.smoothingLowCutoff ((2:ℝ)^N • ξ)‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by linarith [OAI.Analysis.Fourier.LocalSmoothing.norm_smoothingLowCutoff_le_one ξ,
      OAI.Analysis.Fourier.LocalSmoothing.norm_smoothingLowCutoff_le_one ((2:ℝ)^N • ξ)])
  calc
    _ ≤ (‖χ ξ‖*2)*2 := mul_le_mul
      (mul_le_mul_of_nonneg_left he (norm_nonneg _)) hl (norm_nonneg _) (by positivity)
    _ = _ := by ring

end OAI.Analysis.Fourier.WavePackets
