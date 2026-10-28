import OAI.Analysis.Fourier.SquareFunction.BoundaryPartition

/-! Exact finite boundary partitions, with a uniform integrable majorant
for passage through the inverse Fourier integral. -/

namespace OAI.Analysis.Fourier.SquareFunction

open _root_.MeasureTheory Set
open scoped ENNReal

theorem boundary_partition_partial_sum (a u : ℝ) (J N : ℕ) :
    (∑ j ∈ Finset.range N, ((2 : ℝ) ^ (J + j)) ^ (-a) *
      OAI.Analysis.Fourier.BochnerRiesz.positiveDyadicPower a ((2 : ℝ) ^ (J + j) * u)) =
      positiveRadialPower a u *
        (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ J * u) -
          OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ (J + N) * u)) := by
  by_cases hu : 0 < u
  · simpa only [positiveRadialPower, ite_eq_left hu] using
      OAI.Analysis.Fourier.BochnerRiesz.dyadicPower_partial_sum a hu J N
  · have he (j : ℕ) : OAI.Analysis.Fourier.BochnerRiesz.positiveDyadicPower a ((2 : ℝ) ^ (J + j) * u) = 0 := by
      apply ite_eq_right
      exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (by positivity) (le_of_not_gt hu))
    simp only [he, mul_zero, Finset.sum_const_zero, positiveRadialPower, ite_eq_right hu, zero_mul]

theorem amplitude_times_boundary_factor_scaled {α ρ r : ℝ} (hρ : 0 ≤ ρ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (a : ℂ)
    (ha : 1 / 2 ≤ ρ → ρ ≤ 2 →
      a = (2 * α * ρ ^ 2 * r ^ (-2 * α) * (r + ρ) ^ (α - 1) : ℝ))
    {J : ℕ} (hJ : 2 ≤ J) :
    a * (positiveRadialPower (α - 1) (r - ρ) *
      OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ J * (r - ρ)) : ℝ) =
      (radiusMultiplier α ρ r : ℂ) *
        (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ J * (r - ρ)) : ℂ) := by
  by_cases hc : OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ J * (r - ρ)) = 0
  · simp only [hc, mul_zero, Complex.ofReal_zero]
  by_cases hρr : ρ < r
  · have hpow : (4 : ℝ) ≤ 2 ^ J := by
      exact (by norm_num : (4 : ℝ) = 2 ^ (2 : ℕ)).le.trans
        (pow_le_pow_right₀ (by norm_num) hJ)
    have hs : r - ρ < 1 / 2 := by
      by_contra h
      apply hc
      apply OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.zero_of_le_dist
      simp only [OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff, Real.dist_eq, sub_zero]
      exact (show 2 ≤ (2 : ℝ) ^ J * (r - ρ) by nlinarith).trans (le_abs_self _)
    rw [ha (by linarith) (by linarith), radiusMultiplier_eq_positiveRadialPower hρ (by linarith)]
    simp only [Complex.ofReal_mul]
    ring
  · simp only [radiusMultiplier, ite_eq_right hρr, positiveRadialPower,
      ite_eq_right (by linarith : ¬ 0 < r - ρ), zero_mul, Complex.ofReal_zero, mul_zero]

theorem radiusMultiplier_boundary_partial_sum {α ρ r : ℝ} (hρ : 0 ≤ ρ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (a : ℂ)
    (ha : 1 / 2 ≤ ρ → ρ ≤ 2 →
      a = (2 * α * ρ ^ 2 * r ^ (-2 * α) * (r + ρ) ^ (α - 1) : ℝ))
    {J : ℕ} (hJ : 2 ≤ J) (N : ℕ) :
    (∑ j ∈ Finset.range N, Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-(α - 1))) * a *
      OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1) ((2 : ℝ) ^ (J + j) * (r - ρ))) =
      (radiusMultiplier α ρ r : ℂ) *
        ((OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ J * (r - ρ)) : ℂ) -
          (OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ (J + N) * (r - ρ)) : ℂ)) := by
  have he : (∑ j ∈ Finset.range N, Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-(α - 1))) * a *
      OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1) ((2 : ℝ) ^ (J + j) * (r - ρ))) =
      a * ((∑ j ∈ Finset.range N, ((2 : ℝ) ^ (J + j)) ^ (-(α - 1)) *
        OAI.Analysis.Fourier.BochnerRiesz.positiveDyadicPower (α - 1) ((2 : ℝ) ^ (J + j) * (r - ρ))) : ℝ) := by
    simp only [Complex.ofReal_sum, Finset.mul_sum, OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile_apply,
      Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he, boundary_partition_partial_sum, mul_sub, Complex.ofReal_sub, mul_sub,
    amplitude_times_boundary_factor_scaled hρ hr1 hr2 a ha hJ,
    amplitude_times_boundary_factor_scaled hρ hr1 hr2 a ha (show 2 ≤ J + N by omega)]
  ring

theorem norm_radiusMultiplier_boundary_partial_sum {α ρ r : ℝ} (hρ : 0 ≤ ρ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 2) (a : ℂ)
    (ha : 1 / 2 ≤ ρ → ρ ≤ 2 →
      a = (2 * α * ρ ^ 2 * r ^ (-2 * α) * (r + ρ) ^ (α - 1) : ℝ))
    {J : ℕ} (hJ : 2 ≤ J) (N : ℕ) :
    ‖∑ j ∈ Finset.range N, Complex.ofReal (((2 : ℝ) ^ (J + j)) ^ (-(α - 1))) * a *
      OAI.Analysis.Fourier.BochnerRiesz.dyadicPowerProfile (α - 1) ((2 : ℝ) ^ (J + j) * (r - ρ))‖ ≤
      ‖(radiusMultiplier α ρ r : ℂ)‖ := by
  rw [radiusMultiplier_boundary_partial_sum hρ hr1 hr2 a ha hJ, norm_mul]
  apply mul_le_of_le_one_right (norm_nonneg _)
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have h0 : 0 ≤ OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ J * (r - ρ)) :=
    OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.nonneg
  have h1 : OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ J * (r - ρ)) ≤ 1 :=
    OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.le_one
  have h0' : 0 ≤ OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ (J + N) * (r - ρ)) :=
    OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.nonneg
  have h1' : OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff ((2 : ℝ) ^ (J + N) * (r - ρ)) ≤ 1 :=
    OAI.Analysis.Fourier.BochnerRiesz.radialPartitionCutoff.le_one
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end OAI.Analysis.Fourier.SquareFunction
