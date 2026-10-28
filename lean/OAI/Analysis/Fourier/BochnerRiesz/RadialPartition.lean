import OAI.Analysis.Fourier.BochnerRiesz.MaximalShell

open _root_.MeasureTheory Set Metric Filter
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

def radialPartitionCutoff : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

def positiveDyadicPower (δ s : ℝ) : ℝ :=
  if 0 < s then s ^ δ * (radialPartitionCutoff s - radialPartitionCutoff (2 * s)) else 0

theorem positiveDyadicPower_zero_near (δ : ℝ) {s : ℝ} (hs : |s| ≤ 1 / 2) :
    positiveDyadicPower δ s = 0 := by
  have h1 : radialPartitionCutoff s = 1 := radialPartitionCutoff.one_of_mem_closedBall (by
    simpa only [mem_closedBall, dist_zero_right, Real.norm_eq_abs, radialPartitionCutoff] using
      hs.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))
  have h2 : radialPartitionCutoff (2 * s) = 1 := radialPartitionCutoff.one_of_mem_closedBall (by
    simp only [mem_closedBall, dist_zero_right, Real.norm_eq_abs, radialPartitionCutoff]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  simp [positiveDyadicPower, h1, h2]

theorem positiveDyadicPower_zero_far (δ : ℝ) {s : ℝ} (hs : 2 ≤ |s|) :
    positiveDyadicPower δ s = 0 := by
  have h1 : radialPartitionCutoff s = 0 := radialPartitionCutoff.zero_of_le_dist (by
    simpa only [dist_zero_right, Real.norm_eq_abs, radialPartitionCutoff] using hs)
  have h2 : radialPartitionCutoff (2 * s) = 0 := radialPartitionCutoff.zero_of_le_dist (by
    simp only [dist_zero_right, Real.norm_eq_abs, radialPartitionCutoff]
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith)
  simp [positiveDyadicPower, h1, h2]

theorem contDiff_positiveDyadicPower (δ : ℝ) : ContDiff ℝ ∞ (positiveDyadicPower δ) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  by_cases hs : 0 < s
  · have h : ContDiffAt ℝ ∞ (fun t : ℝ ↦ t ^ δ *
        (radialPartitionCutoff t - radialPartitionCutoff (2 * t))) s :=
      (Real.contDiffAt_rpow_const_of_ne hs.ne').mul
        (radialPartitionCutoff.contDiff.contDiffAt.sub
          (radialPartitionCutoff.contDiff.comp (contDiff_const.mul contDiff_id)).contDiffAt)
    apply h.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hs] with t ht
    change 0 < t at ht
    simp only [positiveDyadicPower, ite_eq_left ht]
  · have h : ContDiffAt ℝ ∞ (fun _ : ℝ ↦ (0 : ℝ)) s := contDiffAt_const
    apply h.congr_of_eventuallyEq
    by_cases hs' : s < 0
    · filter_upwards [isOpen_Iio.mem_nhds hs'] with t ht
      change t < 0 at ht
      simp only [positiveDyadicPower, ite_eq_right (not_lt.mpr ht.le)]
    · have he : s = 0 := by linarith
      subst s
      filter_upwards [ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2)] with t ht
      apply positiveDyadicPower_zero_near
      exact le_of_lt (by simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs] using ht)

theorem hasCompactSupport_positiveDyadicPower (δ : ℝ) : HasCompactSupport (positiveDyadicPower δ) := by
  apply (isCompact_closedBall (0 : ℝ) 2).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro s hs
  simp only [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  by_contra h
  exact hs (positiveDyadicPower_zero_far δ (le_of_lt (lt_of_not_ge h)))

theorem hasCompactSupport_complexDyadicPower (δ : ℝ) :
    HasCompactSupport (fun s ↦ (positiveDyadicPower δ s : ℂ)) := by
  change IsCompact (tsupport (fun s ↦ (positiveDyadicPower δ s : ℂ)))
  have he : (Function.support (fun s ↦ (positiveDyadicPower δ s : ℂ))) =
      Function.support (positiveDyadicPower δ) := by
    ext s
    simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
  change IsCompact (closure (Function.support (fun s ↦ (positiveDyadicPower δ s : ℂ))))
  rw [he]
  exact hasCompactSupport_positiveDyadicPower δ

def dyadicPowerProfile (δ : ℝ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_complexDyadicPower δ).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp (contDiff_positiveDyadicPower δ))

theorem dyadicPowerProfile_apply (δ s : ℝ) :
    dyadicPowerProfile δ s = (positiveDyadicPower δ s : ℂ) := rfl

theorem hasCompactSupport_dyadicPowerProfile (δ : ℝ) :
    HasCompactSupport (dyadicPowerProfile δ : ℝ → ℂ) := by
  change HasCompactSupport (fun s ↦ (positiveDyadicPower δ s : ℂ))
  exact hasCompactSupport_complexDyadicPower δ

theorem positiveDyadicPower_support {δ s : ℝ} (hs : positiveDyadicPower δ s ≠ 0) :
    1 / 2 < s ∧ s < 2 := by
  have hpos : 0 < s := by
    by_contra h
    exact hs (by simp [positiveDyadicPower, h])
  constructor
  · by_contra h
    exact hs (positiveDyadicPower_zero_near δ (by rw [abs_of_pos hpos]; linarith))
  · by_contra h
    exact hs (positiveDyadicPower_zero_far δ (by rw [abs_of_pos hpos]; linarith))

theorem dyadicPower_term (δ : ℝ) {s : ℝ} (hs : 0 < s) (j : ℕ) :
    ((2 : ℝ) ^ j) ^ (-δ) * positiveDyadicPower δ ((2 : ℝ) ^ j * s) =
      s ^ δ * (radialPartitionCutoff ((2 : ℝ) ^ j * s) -
        radialPartitionCutoff ((2 : ℝ) ^ (j + 1) * s)) := by
  have hj : 0 < (2 : ℝ) ^ j := by positivity
  rw [positiveDyadicPower, ite_eq_left (mul_pos hj hs), Real.mul_rpow hj.le hs.le]
  have he : 2 * ((2 : ℝ) ^ j * s) = (2 : ℝ) ^ (j + 1) * s := by rw [pow_succ]; ring
  rw [he]
  calc
    _ = (((2 : ℝ) ^ j) ^ (-δ) * ((2 : ℝ) ^ j) ^ δ) *
        (s ^ δ * (radialPartitionCutoff ((2 : ℝ) ^ j * s) -
          radialPartitionCutoff ((2 : ℝ) ^ (j + 1) * s))) := by ring
    _ = _ := by rw [← Real.rpow_add hj, neg_add_cancel, Real.rpow_zero, one_mul]

theorem dyadicPower_partial_sum (δ : ℝ) {s : ℝ} (hs : 0 < s) (J N : ℕ) :
    ∑ j ∈ Finset.range N, ((2 : ℝ) ^ (J + j)) ^ (-δ) * positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * s) =
      s ^ δ * (radialPartitionCutoff ((2 : ℝ) ^ J * s) -
        radialPartitionCutoff ((2 : ℝ) ^ (J + N) * s)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, dyadicPower_term δ hs]
    rw [show J + (N + 1) = J + N + 1 by omega]
    ring

theorem hasSum_dyadicPower_positive (δ : ℝ) {s : ℝ} (hs : 0 < s) (J : ℕ) :
    HasSum (fun j : ℕ ↦ ((2 : ℝ) ^ (J + j)) ^ (-δ) *
      positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * s))
      (s ^ δ * radialPartitionCutoff ((2 : ℝ) ^ J * s)) := by
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (2 / s) (by norm_num : (1 : ℝ) < 2)
  have hlarge (j : ℕ) (hj : N ≤ j) : 2 ≤ (2 : ℝ) ^ (J + j) * s := by
    have hpow : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ (J + j) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hNs : 2 < (2 : ℝ) ^ N * s := (div_lt_iff₀ hs).mp hN
    exact le_of_lt (lt_of_lt_of_le hNs (mul_le_mul_of_nonneg_right hpow hs.le))
  have htail (j : ℕ) (hj : j ∉ Finset.range N) :
      ((2 : ℝ) ^ (J + j)) ^ (-δ) * positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * s) = 0 := by
    have hpos : 0 < (2 : ℝ) ^ (J + j) * s := mul_pos (by positivity) hs
    rw [positiveDyadicPower_zero_far δ (by
      rw [abs_of_pos hpos]
      exact hlarge j (by simpa only [Finset.mem_range, not_lt] using hj)), mul_zero]
  have H : HasSum (fun j : ℕ ↦ ((2 : ℝ) ^ (J + j)) ^ (-δ) *
      positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * s))
      (∑ j ∈ Finset.range N, ((2 : ℝ) ^ (J + j)) ^ (-δ) *
        positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * s)) :=
    hasSum_sum_of_ne_finset_zero htail
  rw [dyadicPower_partial_sum δ hs J N] at H
  have hz : radialPartitionCutoff ((2 : ℝ) ^ (J + N) * s) = 0 :=
    radialPartitionCutoff.zero_of_le_dist (by
      simpa only [dist_zero_right, Real.norm_eq_abs, radialPartitionCutoff] using
        (hlarge N le_rfl).trans (le_abs_self _))
  simpa only [hz, sub_zero] using H

theorem hasSum_dyadicPower {δ : ℝ} (hδ : 0 < δ) (s : ℝ) (J : ℕ) :
    HasSum (fun j : ℕ ↦ ((2 : ℝ) ^ (J + j)) ^ (-δ) *
      positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * s))
      ((max s 0) ^ δ * radialPartitionCutoff ((2 : ℝ) ^ J * s)) := by
  by_cases hs : 0 < s
  · simpa only [max_eq_left hs.le] using hasSum_dyadicPower_positive δ hs J
  · have hs' : s ≤ 0 := le_of_not_gt hs
    have he (j : ℕ) : positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * s) = 0 := by
      have hn : (2 : ℝ) ^ (J + j) * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hs'
      simp only [positiveDyadicPower, ite_eq_right (not_lt.mpr hn)]
    simp only [he, mul_zero, max_eq_right hs', Real.zero_rpow hδ.ne', zero_mul]
    exact hasSum_zero

theorem dyadicPower_partial_sum_all {δ : ℝ} (hδ : 0 < δ) (s : ℝ) (J N : ℕ) :
    ∑ j ∈ Finset.range N, ((2 : ℝ) ^ (J + j)) ^ (-δ) * positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * s) =
      (max s 0) ^ δ * (radialPartitionCutoff ((2 : ℝ) ^ J * s) -
        radialPartitionCutoff ((2 : ℝ) ^ (J + N) * s)) := by
  by_cases hs : 0 < s
  · simpa only [max_eq_left hs.le] using dyadicPower_partial_sum δ hs J N
  · have hs' : s ≤ 0 := le_of_not_gt hs
    have he (j : ℕ) : positiveDyadicPower δ ((2 : ℝ) ^ (J + j) * s) = 0 := by
      have hn : (2 : ℝ) ^ (J + j) * s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hs'
      simp only [positiveDyadicPower, ite_eq_right (not_lt.mpr hn)]
    simp only [he, mul_zero, Finset.sum_const_zero, max_eq_right hs', Real.zero_rpow hδ.ne', zero_mul]

end OAI.Analysis.Fourier.BochnerRiesz
