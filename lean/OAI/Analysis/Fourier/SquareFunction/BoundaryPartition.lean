import OAI.Analysis.Fourier.SquareFunction.Square.L2
import OAI.Analysis.Fourier.BochnerRiesz.RadialPartition

/-! Exact factorization and dyadic partition of the singular boundary factor
in the differentiated Bochner--Riesz multiplier. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

theorem radiusMultiplier_factorization {α ρ r : ℝ}
    (hρ : 0 ≤ ρ) (hr : 0 < r) (hρr : ρ < r) :
    radiusMultiplier α ρ r =
      2 * α * ρ ^ 2 * r ^ (-2 * α) * (r + ρ) ^ (α - 1) * (r - ρ) ^ (α - 1) := by
  have hsq : 0 < r ^ 2 := sq_pos_of_pos hr
  have hminus : 0 < r - ρ := sub_pos.mpr hρr
  have hplus : 0 < r + ρ := by linarith
  have hbase : 1 - ρ ^ 2 / r ^ 2 = ((r - ρ) * (r + ρ)) / r ^ 2 := by
    field_simp
    ; ring
  have hprod : r ^ 2 * (r ^ 2) ^ (α - 1) = r ^ (2 * α) := by
    calc
      _ = (r ^ 2) ^ (α - 1) * r ^ 2 := mul_comm _ _
      _ = (r ^ 2) ^ (α - 1 + 1) := (Real.rpow_add_one hsq.ne' (α - 1)).symm
      _ = _ := by rw [sub_add_cancel, Real.rpow_mul hr.le, Real.rpow_two]
  rw [radiusMultiplier, ite_eq_left hρr, hbase,
    Real.div_rpow (mul_nonneg hminus.le hplus.le) hsq.le,
    Real.mul_rpow hminus.le hplus.le]
  calc
    _ = (2 * α * ρ ^ 2 * (r + ρ) ^ (α - 1) * (r - ρ) ^ (α - 1)) /
        (r ^ 2 * (r ^ 2) ^ (α - 1)) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [hprod, div_eq_mul_inv, ← Real.rpow_neg hr.le]
      rw [show -(2 * α) = -2 * α by ring]
      ring

noncomputable def positiveRadialPower (a u : ℝ) : ℝ :=
  if 0 < u then u ^ a else 0

theorem radiusMultiplier_eq_positiveRadialPower {α ρ r : ℝ}
    (hρ : 0 ≤ ρ) (hr : 0 < r) :
    radiusMultiplier α ρ r =
      (2 * α * ρ ^ 2 * r ^ (-2 * α) * (r + ρ) ^ (α - 1)) *
        positiveRadialPower (α - 1) (r - ρ) := by
  by_cases h : ρ < r
  · rw [positiveRadialPower, ite_eq_left (sub_pos.mpr h)]
    exact radiusMultiplier_factorization hρ hr h
  · simp only [radiusMultiplier, ite_eq_right h, positiveRadialPower,
      ite_eq_right (by linarith : ¬ 0 < r - ρ), mul_zero]

theorem hasSum_boundary_partition (a u : ℝ) (J : ℕ) :
    HasSum (fun j : ℕ => ((2 : ℝ) ^ (J + j)) ^ (-a) *
      OAI.Analysis.Fourier.BochnerRiesz.positiveDyadicPower a ((2 : ℝ) ^ (J + j) * u))
      (positiveRadialPower a u * OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ J * u)) := by
  by_cases hu : 0 < u
  · simpa only [positiveRadialPower, ite_eq_left hu] using
      OAI.Analysis.Fourier.BochnerRiesz.hasSum_dyadicPower_positive a hu J
  · have he (j : ℕ) : OAI.Analysis.Fourier.BochnerRiesz.positiveDyadicPower a ((2 : ℝ) ^ (J + j) * u) = 0 := by
      apply ite_eq_right
      exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hu))
    simp only [he, mul_zero, positiveRadialPower, ite_eq_right hu, zero_mul]
    exact hasSum_zero

theorem amplitude_times_boundary_factor {α ρ r : ℝ} (hρ : 0 ≤ ρ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (a : ℂ)
    (ha : 1 / 2 ≤ ρ → ρ ≤ 2 →
      a = (2 * α * ρ ^ 2 * r ^ (-2 * α) * (r + ρ) ^ (α - 1) : ℝ)) :
    a * (positiveRadialPower (α - 1) (r - ρ) *
      OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ρ)) : ℝ) =
      (radiusMultiplier α ρ r : ℂ) *
        (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ρ)) : ℂ) := by
  by_cases hc : OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ρ)) = 0
  · simp only [hc, mul_zero, Complex.ofReal_zero]
  by_cases hρr : ρ < r
  · have hs : r - ρ < 1 / 2 := by
      by_contra h
      apply hc
      apply OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.zero_of_le_dist
      simp only [OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff, Real.dist_eq, sub_zero]
      exact (show 2 ≤ 4 * (r - ρ) by linarith).trans (le_abs_self _)
    rw [ha (by linarith) (by linarith), radiusMultiplier_eq_positiveRadialPower hρ (by linarith)]
    simp only [Complex.ofReal_mul]
    ring
  · simp only [radiusMultiplier, ite_eq_right hρr, positiveRadialPower,
      ite_eq_right (by linarith : ¬ 0 < r - ρ), zero_mul, Complex.ofReal_zero, mul_zero]

theorem hasSum_radiusMultiplier_boundary {α ρ r : ℝ} (hρ : 0 ≤ ρ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (a : ℂ)
    (ha : 1 / 2 ≤ ρ → ρ ≤ 2 →
      a = (2 * α * ρ ^ 2 * r ^ (-2 * α) * (r + ρ) ^ (α - 1) : ℝ)) :
    HasSum (fun j : ℕ =>
      Complex.ofReal (((2 : ℝ) ^ (2 + j)) ^ (-(α - 1))) * a *
        OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1) ((2 : ℝ) ^ (2 + j) * (r - ρ)))
      ((radiusMultiplier α ρ r : ℂ) *
        (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff (4 * (r - ρ)) : ℂ)) := by
  have H := (Complex.hasSum_ofReal.mpr (hasSum_boundary_partition (α - 1) (r - ρ) 2)).mul_left a
  rw [show (2 : ℝ) ^ 2 = 4 by norm_num] at H
  rw [amplitude_times_boundary_factor hρ hr1 hr2 a ha] at H
  convert H using 1
  ext j
  rw [OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile_apply, Complex.ofReal_mul]
  ring

end OAI.Analysis.Fourier.SquareFunction
