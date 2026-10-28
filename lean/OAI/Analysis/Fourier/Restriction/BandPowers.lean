import OAI.Analysis.Fourier.BochnerRiesz.Geometric

open _root_.MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem pow_mul_rpow_band {b : ℝ} (hb : 0 < b) (k : ℕ) (t : ℝ) :
    b ^ k * (b ^ k) ^ t = (b ^ (1 + t)) ^ k := by
  calc
    _ = (b ^ k) ^ (1 + t) := by rw [Real.rpow_add (pow_pos hb k), Real.rpow_one]
    _ = _ := by
      rw [← Real.rpow_natCast_mul hb.le,
        show (k : ℝ) * (1 + t) = (1 + t) * k by ring,
        Real.rpow_mul_natCast hb.le]

theorem high_band_weight {b : ℝ} (hb : 0 < b) (k : ℕ) (t : ℝ) :
    b ^ (k + 1) * (b ^ k) ^ t = b * (b ^ (1 + t)) ^ k := by
  rw [pow_succ]
  calc
    _ = b * (b ^ k * (b ^ k) ^ t) := by ring
    _ = _ := by rw [pow_mul_rpow_band hb]

theorem low_band_weight {b : ℝ} (hb : 0 < b) (k : ℕ) (t : ℝ) :
    b ^ k * (b ^ (k + 1)) ^ t = b ^ t * (b ^ (1 + t)) ^ k := by
  rw [pow_succ, Real.mul_rpow (pow_nonneg hb.le k) hb.le]
  calc
    _ = b ^ t * (b ^ k * (b ^ k) ^ t) := by ring
    _ = _ := by rw [pow_mul_rpow_band hb]

theorem sum_mul_ofReal_geometric_le (A : ℝ≥0∞) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (N : ℕ) :
    (∑ k ∈ Finset.range N, A * ENNReal.ofReal (r ^ k)) ≤
      A * ENNReal.ofReal ((1 - r)⁻¹) := by
  rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ pow_nonneg hr0 k)]
  apply mul_le_mul le_rfl _ zero_le zero_le
  apply ENNReal.ofReal_le_ofReal
  simpa only [zero_add] using OAI.Analysis.Fourier.BochnerRiesz.sum_geometric_shift_le hr0 hr1 0 N

end OAI.Analysis.Fourier.Restriction
