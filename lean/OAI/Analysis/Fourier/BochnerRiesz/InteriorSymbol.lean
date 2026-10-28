import OAI.Analysis.Fourier.BochnerRiesz.RadialPartition

open OAI.Analysis.Fourier.Wave

open Set Metric Filter _root_.MeasureTheory
open scoped ENNReal ContDiff Topology
noncomputable section
namespace OAI.Analysis.Fourier.BochnerRiesz

theorem contDiffAt_bochnerRieszSymbol_unit {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {ξ : Space n} (hξ : ‖ξ‖ ≠ 1) :
    ContDiffAt ℝ ∞ (OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1) ξ := by
  rcases lt_or_gt_of_ne hξ with hin | hout
  · have hbase : (1 : ℝ) - ‖ξ‖ ^ 2 ≠ 0 := by nlinarith [norm_nonneg ξ]
    have H : ContDiffAt ℝ ∞ (fun y : Space n ↦ (1 - ‖y‖ ^ 2) ^ δ) ξ :=
      (contDiffAt_const.sub (contDiffAt_id.norm_sq ℝ)).rpow_const_of_ne hbase
    apply H.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hin] with y hy
    change ‖y‖ < 1 at hy
    have hb : 0 ≤ 1 - ‖y‖ ^ 2 := by nlinarith [norm_nonneg y]
    simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, div_one, max_eq_left hb]
  · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hout] with y hy
    change 1 < ‖y‖ at hy
    have hb : 1 - ‖y‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg y]
    simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, div_one, max_eq_right hb, Real.zero_rpow hδ.ne']

def brInteriorReal {n : ℕ} (δ : ℝ) (J : ℕ) (ξ : Space n) : ℝ :=
  OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ * (1 - radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖ξ‖)))

theorem two_pow_ge_four {J : ℕ} (hJ : 2 ≤ J) : (4 : ℝ) ≤ 2 ^ J := by
  calc
    (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hJ

theorem contDiff_brInteriorReal {n : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {J : ℕ} (hJ : 2 ≤ J) : ContDiff ℝ ∞ (brInteriorReal (n := n) δ J) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hzero : ξ = 0
  · subst ξ
    have H := contDiffAt_bochnerRieszSymbol_unit (n := n) hδ (ξ := 0) (by simp)
    apply H.congr_of_eventuallyEq
    filter_upwards [ball_mem_nhds (0 : Space n) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    have hy' : ‖y‖ < 1 / 2 := by simpa only [mem_ball, dist_zero_right] using hy
    have harg : 2 ≤ (2 : ℝ) ^ J * (1 - ‖y‖) := by
      nlinarith [two_pow_ge_four hJ, norm_nonneg y]
    have hz : radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖y‖)) = 0 :=
      radialPartitionCutoff.zero_of_le_dist (by
        simpa only [radialPartitionCutoff, dist_zero_right, Real.norm_eq_abs,
          abs_of_nonneg (by linarith : 0 ≤ (2 : ℝ) ^ J * (1 - ‖y‖))] using harg)
    simp only [brInteriorReal, hz, sub_zero, mul_one]
  · by_cases hunit : ‖ξ‖ = 1
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      have hcont : Continuous (fun y : Space n ↦ |(2 : ℝ) ^ J * (1 - ‖y‖)|) := by fun_prop
      have hlt : |(2 : ℝ) ^ J * (1 - ‖ξ‖)| < 1 := by simp [hunit]
      filter_upwards [(isOpen_lt hcont continuous_const).mem_nhds hlt] with y hy
      change |(2 : ℝ) ^ J * (1 - ‖y‖)| < 1 at hy
      have ho : radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖y‖)) = 1 :=
        radialPartitionCutoff.one_of_mem_closedBall (by
          simpa only [radialPartitionCutoff, mem_closedBall, dist_zero_right, Real.norm_eq_abs] using hy.le)
      simp only [brInteriorReal, ho, sub_self, mul_zero]
    · exact (contDiffAt_bochnerRieszSymbol_unit hδ hunit).mul
        (contDiffAt_const.sub (radialPartitionCutoff.contDiff.contDiffAt.comp ξ
          (contDiffAt_const.mul (contDiffAt_const.sub (contDiffAt_norm ℝ hzero)))))

theorem hasCompactSupport_brInteriorReal {n : ℕ} {δ : ℝ} (hδ : 0 < δ) (J : ℕ) :
    HasCompactSupport (brInteriorReal (n := n) δ J) := by
  apply (isCompact_closedBall (0 : Space n) 1).of_isClosed_subset isClosed_closure
  apply closure_minimal _ isClosed_closedBall
  intro ξ hξ
  simp only [mem_closedBall, dist_zero_right]
  by_contra h
  have hn : 1 < ‖ξ‖ := lt_of_not_ge h
  have hb : 1 - ‖ξ‖ ^ 2 ≤ 0 := by nlinarith [norm_nonneg ξ]
  exact hξ (by simp only [brInteriorReal, OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, div_one, max_eq_right hb,
    Real.zero_rpow hδ.ne', zero_mul])

def brExteriorSymbol {n : ℕ} (δ : ℝ) (χ : Space n → ℂ) (ξ : Space n) : ℂ :=
  χ ξ * ((1 + ‖ξ‖) ^ δ : ℝ)

theorem contDiff_brExteriorSymbol {n : ℕ} (δ : ℝ) {χ : Space n → ℂ}
    (hχ : ContDiff ℝ ∞ χ) (hzero : (0 : Space n) ∉ tsupport χ) :
    ContDiff ℝ ∞ (brExteriorSymbol δ χ) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hs : ξ ∈ tsupport χ
  · have hξ : ξ ≠ 0 := by intro h; subst ξ; exact hzero hs
    have hpos : 0 < 1 + ‖ξ‖ := by positivity
    exact hχ.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp ξ
      ((contDiffAt_const.add (contDiffAt_norm ℝ hξ)).rpow_const_of_ne hpos.ne'))
  · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hs] with y hy
    simp only [brExteriorSymbol, hy, Pi.zero_apply, zero_mul]

theorem hasCompactSupport_brExteriorSymbol {n : ℕ} (δ : ℝ) {χ : Space n → ℂ}
    (hc : HasCompactSupport χ) : HasCompactSupport (brExteriorSymbol δ χ) := hc.mul_right

theorem radialCutoff_support_annulus {n : ℕ} {J : ℕ} (hJ : 2 ≤ J) {ξ : Space n}
    (hξ : radialPartitionCutoff ((2 : ℝ) ^ J * (1 - ‖ξ‖)) ≠ 0) :
    1 / 2 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2 := by
  have hm : (2 : ℝ) ^ J * (1 - ‖ξ‖) ∈ Function.support radialPartitionCutoff := hξ
  rw [radialPartitionCutoff.support_eq] at hm
  have ha : |(2 : ℝ) ^ J * (1 - ‖ξ‖)| < 2 := by
    simpa only [radialPartitionCutoff, mem_ball, dist_zero_right, Real.norm_eq_abs] using hm
  have hs := abs_lt.mp ha
  have hpow := two_pow_ge_four hJ
  constructor <;> nlinarith [norm_nonneg ξ]

theorem bochnerRieszSymbol_unit_factor {n : ℕ} (δ : ℝ) (ξ : Space n) :
    OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol δ 1 ξ = (1 + ‖ξ‖) ^ δ * (max (1 - ‖ξ‖) 0) ^ δ := by
  have hbase : max (1 - ‖ξ‖ ^ 2) 0 = (1 + ‖ξ‖) * max (1 - ‖ξ‖) 0 := by
    by_cases h : ‖ξ‖ ≤ 1
    · rw [max_eq_left (by nlinarith [norm_nonneg ξ]), max_eq_left (by linarith)]
      ring
    · have hn : 1 < ‖ξ‖ := lt_of_not_ge h
      rw [max_eq_right (by nlinarith [norm_nonneg ξ]), max_eq_right (by linarith), mul_zero]
  simp only [OAI.Analysis.Fourier.BochnerRiesz.bochnerRieszSymbol, div_one, hbase]
  exact Real.mul_rpow (by positivity) (le_max_right _ _)

end OAI.Analysis.Fourier.BochnerRiesz
