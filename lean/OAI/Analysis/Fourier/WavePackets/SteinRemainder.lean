import OAI.Analysis.Fourier.SquareFunction.Square.L2
import OAI.Analysis.Fourier.BochnerRiesz.RadialPartition

open OAI.Analysis.Fourier.Wave

namespace OAI.Analysis.Fourier.WavePackets

open Set Metric Filter
open scoped ContDiff Topology

noncomputable def steinRemainder {n : ℕ} (α : ℝ) (p : ℝ × Space n) : ℝ :=
  if ‖p.2‖ < p.1 then
    2 * α / p.1 ^ 2 * (1 - ‖p.2‖ ^ 2 / p.1 ^ 2) ^ (α - 1) *
      (1 - OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (p.1 - ‖p.2‖)))
  else 0

theorem steinRemainder_zero_near_cone {n : ℕ} (α : ℝ) {p : ℝ × Space n}
    (hp : p.1 - ‖p.2‖ < 1 / 4) : steinRemainder α p = 0 := by
  by_cases h : ‖p.2‖ < p.1
  · have hc : OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (p.1 - ‖p.2‖)) = 1 :=
      OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.one_of_mem_closedBall (by
        simp only [mem_closedBall, Real.dist_eq, sub_zero, OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff]
        exact abs_le.mpr ⟨by linarith, by linarith⟩)
    simp [steinRemainder, h, hc]
  · simp [steinRemainder, h]

theorem steinRemainder_eq_without_cutoff {n : ℕ} (α : ℝ) {p : ℝ × Space n}
    (hp : 1 / 2 < p.1 - ‖p.2‖) :
    steinRemainder α p = 2 * α / p.1 ^ 2 *
      (1 - ‖p.2‖ ^ 2 / p.1 ^ 2) ^ (α - 1) := by
  have hc : OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (p.1 - ‖p.2‖)) = 0 :=
    OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.zero_of_le_dist (by
      simp only [Real.dist_eq, sub_zero, OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff]
      rw [abs_of_pos (by linarith)]
      linarith)
  simp [steinRemainder, show ‖p.2‖ < p.1 by linarith, hc]

theorem contDiffAt_steinRemainder {n : ℕ} (α : ℝ) {p : ℝ × Space n}
    (hr : 1 / 2 < p.1) : ContDiffAt ℝ ∞ (steinRemainder α) p := by
  have hgap : Continuous (fun q : ℝ × Space n => q.1 - ‖q.2‖) :=
    continuous_fst.sub continuous_snd.norm
  by_cases hnear : p.1 - ‖p.2‖ < 1 / 4
  · apply (show ContDiffAt ℝ ∞ (fun _ : ℝ × Space n => (0 : ℝ)) p from
      contDiffAt_const).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt hgap continuous_const).mem_nhds hnear] with q hq
    exact steinRemainder_zero_near_cone α hq
  have hρ : ‖p.2‖ < p.1 := by linarith
  have hr0 : p.1 ≠ 0 := by linarith
  have hbase : 0 < 1 - ‖p.2‖ ^ 2 / p.1 ^ 2 := by
    have hr2 : 0 < p.1 ^ 2 := sq_pos_of_ne_zero hr0
    have hsq : ‖p.2‖ ^ 2 < p.1 ^ 2 := by nlinarith [norm_nonneg p.2]
    have hd : ‖p.2‖ ^ 2 / p.1 ^ 2 < 1 := (div_lt_one hr2).mpr hsq
    linarith
  have hden : ContDiffAt ℝ ∞ (fun q : ℝ × Space n => q.1 ^ 2) p :=
    contDiffAt_fst.pow 2
  have hnzero : (fun q : ℝ × Space n => q.1 ^ 2) p ≠ 0 := pow_ne_zero 2 hr0
  have hrat : ContDiffAt ℝ ∞ (fun q : ℝ × Space n => 2 * α / q.1 ^ 2) p :=
    contDiffAt_const.div hden hnzero
  have hinner : ContDiffAt ℝ ∞ (fun q : ℝ × Space n =>
      1 - ‖q.2‖ ^ 2 / q.1 ^ 2) p :=
    contDiffAt_const.sub ((contDiffAt_snd.norm_sq ℝ).div hden hnzero)
  have hmain : ContDiffAt ℝ ∞ (fun q : ℝ × Space n =>
      2 * α / q.1 ^ 2 * (1 - ‖q.2‖ ^ 2 / q.1 ^ 2) ^ (α - 1)) p :=
    hrat.mul (hinner.rpow_const_of_ne hbase.ne')
  by_cases hz : p.2 = 0
  · apply hmain.congr_of_eventuallyEq
    have hlarge : 1 / 2 < p.1 - ‖p.2‖ := by simpa [hz] using hr
    filter_upwards [(isOpen_lt continuous_const hgap).mem_nhds hlarge] with q hq
    exact steinRemainder_eq_without_cutoff α hq
  · have hnorm : ContDiffAt ℝ ∞ (fun q : ℝ × Space n => ‖q.2‖) p :=
      (contDiffAt_norm ℝ hz).comp p contDiffAt_snd
    have hc : ContDiffAt ℝ ∞ (fun q : ℝ × Space n =>
        1 - OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (q.1 - ‖q.2‖))) p :=
      contDiffAt_const.sub (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.contDiff.comp_contDiffAt p
        (contDiffAt_const.mul (contDiffAt_fst.sub hnorm)))
    apply (hmain.mul hc).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_snd.norm continuous_fst).mem_nhds hρ] with q hq
    simp only [steinRemainder, ite_eq_left hq]

/-- Smooth compact low-frequency remainder after removal of the singular
boundary shells, with the quadratic zero at the origin factored out. -/
theorem exists_stein_remainder (n : ℕ) (α : ℝ) :
    ∃ C : ℝ × Space n → ℂ, ContDiff ℝ ∞ C ∧ HasCompactSupport C ∧
      (∀ r ξ, 1 ≤ r → r ≤ 2 →
        (‖ξ‖ ^ 2 : ℝ) * C (r, ξ) =
          (OAI.Analysis.Fourier.SquareFunction.radiusMultiplier α ‖ξ‖ r : ℂ) *
            (1 - (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ‖ξ‖)) : ℂ))) ∧
      (∀ r ξ, 3 ≤ ‖ξ‖ → C (r, ξ) = 0) := by
  let β : ContDiffBump (3 / 2 : ℝ) :=
    { rIn := 1 / 2, rOut := 3 / 4, rIn_pos := by norm_num,
      rIn_lt_rOut := by norm_num }
  let C : ℝ × Space n → ℂ := fun p => (β p.1 * steinRemainder α p : ℝ)
  have hβ0 {r : ℝ} (hr : r ≤ 1 / 2) : r ∉ tsupport (β : ℝ → ℝ) := by
    rw [β.tsupport_eq]
    intro h
    have ht : |r - 3 / 2| ≤ 3 / 4 := by
      simpa only [mem_closedBall, Real.dist_eq, β] using h
    have := (abs_le.mp ht).1
    linarith
  have hCn {r : ℝ} {ξ : Space n} (hn : C (r, ξ) ≠ 0) :
      |r - 3 / 2| < 3 / 4 ∧ ‖ξ‖ < r := by
    have hb : β r ≠ 0 := by intro h; exact hn (by simp [C, h])
    have hg : ‖ξ‖ < r := by
      by_contra h
      exact hn (by simp [C, steinRemainder, h])
    refine ⟨?_, hg⟩
    have hs : r ∈ Function.support β := hb
    simpa only [β.support_eq, mem_ball, Real.dist_eq, β] using hs
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro p
    by_cases hr : 1 / 2 < p.1
    · exact Complex.ofRealCLM.contDiff.comp_contDiffAt p
        (((β.contDiff.comp contDiff_fst).contDiffAt).mul (contDiffAt_steinRemainder α hr))
    · apply (show ContDiffAt ℝ ∞ (fun _ : ℝ × Space n => (0 : ℂ)) p from
        contDiffAt_const).congr_of_eventuallyEq
      filter_upwards [(notMem_tsupport_iff_eventuallyEq.mp (hβ0 (le_of_not_gt hr))).comp_tendsto
        continuousAt_fst] with q hq
      change β q.1 = 0 at hq
      simp [C, hq]
  · apply HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall (3 / 2 : ℝ) (3 / 4)).prod
        (isCompact_closedBall (0 : Space n) 3))
    rintro ⟨r, ξ⟩ hn
    have hs := hCn hn
    refine ⟨?_, ?_⟩
    · simpa only [mem_closedBall, Real.dist_eq] using hs.1.le
    · simp only [mem_closedBall, dist_zero_right]
      have := (abs_lt.mp hs.1).2
      linarith
  · intro r ξ hr1 hr2
    have hb : β r = 1 := β.one_of_mem_closedBall (by
      simp only [mem_closedBall, Real.dist_eq, β]
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
    by_cases hg : ‖ξ‖ < r
    · simp only [C, hb, one_mul, steinRemainder, hg, ite_true,
        OAI.Analysis.Fourier.SquareFunction.radiusMultiplier]
      push_cast
      ring
    · simp [C, steinRemainder, OAI.Analysis.Fourier.SquareFunction.radiusMultiplier, hg]
  · intro r ξ hξ
    by_contra hn
    have hs := hCn hn
    have := (abs_lt.mp hs.1).2
    linarith

end OAI.Analysis.Fourier.WavePackets
