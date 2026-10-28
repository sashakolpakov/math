import OAI.Analysis.Fourier.LocalSmoothing.DyadicCutoff
import OAI.Analysis.Fourier.BochnerRiesz.Cutoff

open OAI.Analysis.Fourier.Wave

open Set Metric
open scoped ContDiff
noncomputable section
namespace OAI.Analysis.Fourier.LocalSmoothing

theorem smoothingLowCutoff_eq_one_of_norm_le_eight {n : ℕ} {ξ : Space n}
    (hξ : ‖ξ‖ ≤ 8) : smoothingLowCutoff ξ = 1 := by
  have h := (smoothingLowBump n).one_of_mem_closedBall (by
    simpa only [mem_closedBall, dist_zero_right, smoothingLowBump] using hξ)
  simp only [smoothingLowCutoff, h, Complex.ofReal_one]

theorem smoothingLowCutoff_eq_zero_of_sixteen_le_norm {n : ℕ} {ξ : Space n}
    (hξ : 16 ≤ ‖ξ‖) : smoothingLowCutoff ξ = 0 := by
  have h := (smoothingLowBump n).zero_of_le_dist (by
    simpa only [dist_zero_right, smoothingLowBump] using hξ)
  simp only [smoothingLowCutoff, h, Complex.ofReal_zero]

theorem smoothingAnnularCutoff_eq_zero_of_norm_le_eight {n : ℕ} {ξ : Space n}
    (hξ : ‖ξ‖ ≤ 8) : smoothingAnnularCutoff ξ = 0 := by
  have hh : ‖(1 / 2 : ℝ) • ξ‖ ≤ 8 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith [norm_nonneg ξ]
  simp only [smoothingAnnularCutoff, smoothingLowCutoff_eq_one_of_norm_le_eight hh,
    smoothingLowCutoff_eq_one_of_norm_le_eight hξ, sub_self]

theorem smoothingAnnularCutoff_eq_zero_of_thirtyTwo_le_norm {n : ℕ} {ξ : Space n}
    (hξ : 32 ≤ ‖ξ‖) : smoothingAnnularCutoff ξ = 0 := by
  have hh : 16 ≤ ‖(1 / 2 : ℝ) • ξ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  simp only [smoothingAnnularCutoff, smoothingLowCutoff_eq_zero_of_sixteen_le_norm hh,
    smoothingLowCutoff_eq_zero_of_sixteen_le_norm (by linarith : 16 ≤ ‖ξ‖), sub_self]

theorem tsupport_smoothingAnnularCutoff_subset (n : ℕ) :
    tsupport (@smoothingAnnularCutoff n) ⊆ {ξ : Space n | 8 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 32} := by
  apply closure_minimal _
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
  intro ξ hξ
  change 8 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 32
  constructor
  · by_contra! hsmall
    exact hξ (smoothingAnnularCutoff_eq_zero_of_norm_le_eight hsmall.le)
  · by_contra! hlarge
    exact hξ (smoothingAnnularCutoff_eq_zero_of_thirtyTwo_le_norm hlarge.le)

/-- An enlarged annular cutoff, separated far enough from zero for the
logarithmic normalizing family used in Sobolev summation. -/
theorem exists_smoothing_enlarged_cutoff (n : ℕ) :
    ∃ χ : Space n → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (0 : Space n) ∉ tsupport χ ∧
      (∀ ξ, smoothingAnnularCutoff ξ ≠ 0 → χ ξ = 1) ∧
      (∀ ξ, ‖ξ‖ ≤ 4 → χ ξ = 0) := by
  obtain ⟨χ, hχ, hc, hz, hone, hband⟩ := OAI.Analysis.Fourier.BochnerRiesz.exists_annular_cutoff
    (n := n) (a := 4) (b := 8) (c := 32) (d := 64)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨χ, hχ, hc, hz, ?_, ?_⟩
  · intro ξ hξ
    have h := tsupport_smoothingAnnularCutoff_subset n (subset_closure hξ)
    exact hone ξ h.1 h.2
  · intro ξ hξ
    by_contra hn
    exact (not_lt_of_ge hξ) (hband ξ hn).1

end OAI.Analysis.Fourier.LocalSmoothing
