import OAI.Analysis.Fourier.BochnerRiesz.InteriorSymbol

open OAI.Analysis.Fourier.Wave

open Set Metric Filter _root_.MeasureTheory
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem bochnerRieszSymbol_unit_mem_Icc {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (ξ : Space n) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ ∈ Icc (0 : ℝ) 1 := by
  simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, div_one, mem_Icc]
  have h0 : 0 ≤ max (1 - ‖ξ‖ ^ 2) 0 := le_max_right _ _
  have h1 : max (1 - ‖ξ‖ ^ 2) 0 ≤ 1 := max_le (by nlinarith [sq_nonneg ‖ξ‖]) (by norm_num)
  exact ⟨Real.rpow_nonneg h0 _, Real.rpow_le_one h0 h1 hδ⟩

theorem brInteriorReal_mem_Icc {n : ℕ} {δ : ℝ} (hδ : 0 ≤ δ) (J : ℕ) (ξ : Space n) :
    brInteriorReal δ J ξ ∈ Icc (0 : ℝ) 1 := by
  obtain ⟨h0, h1⟩ := bochnerRieszSymbol_unit_mem_Icc hδ ξ
  have hc0 : 0 ≤ radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖ξ‖)) := radialPartitionCutoff.nonneg
  have hc1 : radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖ξ‖)) ≤ 1 := radialPartitionCutoff.le_one
  constructor
  · exact mul_nonneg h0 (sub_nonneg.mpr hc1)
  · dsimp only [brInteriorReal]
    nlinarith

theorem eventually_brInteriorReal_eq {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (J : ℕ) (ξ : Space n) :
    ∀ᶠ N : ℕ in atTop, brInteriorReal δ (J + N) ξ = OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ := by
  by_cases hunit : ‖ξ‖ = 1
  · exact Eventually.of_forall (fun N ↦ by
      simp only [brInteriorReal, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, div_one, hunit, one_pow, sub_self,
        max_self, Real.zero_rpow hδ.ne', zero_mul])
  · have hs : 0 < |1 - ‖ξ‖| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hunit))
    obtain ⟨M, hM⟩ := pow_unbounded_of_one_lt (2 / |1 - ‖ξ‖|) (by norm_num : (1 : ℝ) < 2)
    filter_upwards [eventually_ge_atTop M] with N hN
    have hpow : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ (J + N) := pow_le_pow_right₀ (by norm_num) (by omega)
    have harg : 2 ≤ |(2 : ℝ) ^ (J + N) * (1 - ‖ξ‖)| := by
      rw [abs_mul, abs_of_pos (pow_pos (by norm_num) _)]
      exact ((div_lt_iff₀ hs).mp hM).le.trans (mul_le_mul_of_nonneg_right hpow hs.le)
    have hz : radialPartitionCutoff ((2 : ℝ) ^ (J + N) * (1 - ‖ξ‖)) = 0 :=
      radialPartitionCutoff.zero_of_le_dist (by
        simpa only [radialPartitionCutoff, dist_zero_right, Real.norm_eq_abs] using harg)
    simp only [brInteriorReal, hz, sub_zero, mul_one]

theorem tendsto_brInteriorReal {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (J : ℕ) (ξ : Space n) :
    Tendsto (fun N : ℕ ↦ brInteriorReal δ (J + N) ξ) atTop (𝓝 (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_brInteriorReal_eq hδ J ξ] with N hN
  exact hN.symm

end OAI.Analysis.Fourier.BochnerRiesz
