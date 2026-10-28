import OAI.Analysis.Fourier.Restriction.Translations

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal RealInnerProductSpace
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

/-- The far-field distance differs from its linear phase by a quadratic error. -/
theorem farField_distance_error {n : ℕ} {ω y : Space n} (hω : ‖ω‖ = 1)
    {t : ℝ} (ht : 0 < t) (hy : ‖y‖ ≤ t / 2) :
    |‖t • ω - y‖ - t + inner ℝ ω y| ≤ ‖y‖ ^ 2 / t := by
  have hi : |inner ℝ ω y| ≤ ‖y‖ := by
    simpa only [hω, one_mul] using abs_real_inner_le_norm ω y
  have htω : ‖t • ω‖ = t := by simp [norm_smul, hω, abs_of_pos ht]
  have ha : t / 2 ≤ ‖t • ω - y‖ := by
    have H := norm_sub_norm_le (t • ω) y
    rw [htω] at H
    linarith
  have hb : t / 2 ≤ t - inner ℝ ω y := by
    have := (abs_le.mp hi).2
    linarith
  have hs : ‖t • ω - y‖ ^ 2 =
      t ^ 2 - 2 * t * inner ℝ ω y + ‖y‖ ^ 2 := by
    rw [norm_sub_sq_real, htω, real_inner_smul_left]
    ring
  have hisq : (inner ℝ ω y) ^ 2 ≤ ‖y‖ ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hi
  have hd : 0 ≤ ‖t • ω - y‖ - t + inner ℝ ω y := by
    nlinarith [norm_nonneg (t • ω - y)]
  rw [abs_of_nonneg hd, le_div_iff₀ ht]
  have H := mul_nonneg hd (show 0 ≤ ‖t • ω - y‖ + (t - inner ℝ ω y) - t by linarith)
  nlinarith

theorem farField_norm_comparable {n : ℕ} {ω y : Space n} (hω : ‖ω‖ = 1)
    {t : ℝ} (ht : 0 < t) (hy : ‖y‖ ≤ t / 2) :
    t / 2 ≤ ‖t • ω - y‖ ∧ ‖t • ω - y‖ ≤ 3 * t / 2 := by
  have htω : ‖t • ω‖ = t := by simp [norm_smul, hω, abs_of_pos ht]
  have H := norm_sub_norm_le (t • ω) y
  have J := norm_sub_le (t • ω) y
  rw [htω] at H J
  constructor <;> linarith

theorem farField_norm_ratio {n : ℕ} {ω y : Space n} (hω : ‖ω‖ = 1)
    {t : ℝ} (ht : 0 < t) :
    |‖t • ω - y‖ / t - 1| ≤ ‖y‖ / t := by
  have htω : ‖t • ω‖ = t := by simp [norm_smul, hω, abs_of_pos ht]
  have H := norm_sub_norm_le (t • ω) y
  have J := norm_sub_le (t • ω) y
  rw [htω] at H J
  have he : ‖t • ω - y‖ / t - 1 = (‖t • ω - y‖ - t) / t := by
    field_simp
  rw [he, abs_div, abs_of_pos ht, div_le_div_iff_of_pos_right ht, abs_le]
  constructor <;> linarith

end OAI.Analysis.Fourier.Restriction
