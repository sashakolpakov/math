import OAI.Analysis.Fourier.Restriction.ProductNorm

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem radial_jacobian_factor (n : ℕ) {T : ℝ} (hT : 0 < T) (p : ℝ) :
    ((ENNReal.ofReal (T ^ (n - 1)))⁻¹) ^ (1 / p) =
      ENNReal.ofReal T ^ (-((n - 1 : ℕ) : ℝ) / p) := by
  rw [ENNReal.ofReal_pow hT.le, ← ENNReal.rpow_natCast, ← ENNReal.rpow_neg, ← ENNReal.rpow_mul]
  congr 1
  ring

theorem annular_time_rate {n : ℕ} (hn : 1 ≤ n) {T : ℝ} (hT : 0 < T) (p β : ℝ) :
    (ENNReal.ofReal T ^ (1 / p))⁻¹ *
      (ENNReal.ofReal ((3 * T) ^ β) *
        (2 * ((ENNReal.ofReal (T ^ (n - 1)))⁻¹) ^ (1 / p))) =
      ENNReal.ofReal (2 * 3 ^ β * T ^ (β - (n : ℝ) / p)) := by
  rw [← ENNReal.rpow_neg, radial_jacobian_factor n hT]
  simp only [ENNReal.ofReal_rpow_of_pos hT]
  have he : T ^ (-(1 / p)) * ((3 * T) ^ β * (2 * T ^ (-((n - 1 : ℕ) : ℝ) / p))) =
      2 * 3 ^ β * T ^ (β - (n : ℝ) / p) := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hT.le]
    calc
      _ = 2 * 3 ^ β * (T ^ (-(1 / p)) * T ^ β * T ^ (-((n - 1 : ℕ) : ℝ) / p)) := by ring
      _ = 2 * 3 ^ β * T ^ (-(1 / p) + β + -((n - 1 : ℕ) : ℝ) / p) := by
        rw [← Real.rpow_add hT, ← Real.rpow_add hT]
      _ = _ := by
        congr 2
        rw [Nat.cast_sub hn]
        push_cast
        ring
  rw [← he]
  simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ T ^ (-(1 / p))),
    ENNReal.ofReal_mul (by positivity : 0 ≤ (3 * T) ^ β),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

theorem annular_time_mass_cancel {T p : ℝ} (hT : 0 < T) (hp : 0 < p) (m : ℝ≥0∞) :
    (ENNReal.ofReal T ^ (1 / p))⁻¹ * (m * ENNReal.ofReal T) ^ (1 / p) = m ^ (1 / p) := by
  have hc : ENNReal.ofReal T ^ (1 / p) ≠ 0 :=
    ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hT) ENNReal.ofReal_ne_top)
  have hct : ENNReal.ofReal T ^ (1 / p) ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity : 0 ≤ 1 / p), mul_left_comm,
    ENNReal.inv_mul_cancel hc hct, mul_one]

theorem annular_inequality_normalize {n : ℕ} (hn : 1 ≤ n) {T p : ℝ}
    (hT : 0 < T) (hp : 0 < p) (β : ℝ) (c F U E m : ℝ≥0∞)
    (h : c * (F * ENNReal.ofReal T ^ (1 / p)) ≤
      ENNReal.ofReal ((3 * T) ^ β) *
        (2 * (((ENNReal.ofReal (T ^ (n - 1)))⁻¹) ^ (1 / p) * U)) +
      E * (m * ENNReal.ofReal T) ^ (1 / p)) :
    c * F ≤ ENNReal.ofReal (2 * 3 ^ β * T ^ (β - (n : ℝ) / p)) * U + E * m ^ (1 / p) := by
  let v := ENNReal.ofReal T ^ (1 / p)
  have hv : v ≠ 0 := ne_of_gt (ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hT) ENNReal.ofReal_ne_top)
  have hvt : v ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
  calc
    c * F = v⁻¹ * (c * (F * v)) := by
      calc
        _ = c * F * (v⁻¹ * v) := by rw [ENNReal.inv_mul_cancel hv hvt, mul_one]
        _ = _ := by ring
    _ ≤ v⁻¹ * (ENNReal.ofReal ((3 * T) ^ β) *
        (2 * (((ENNReal.ofReal (T ^ (n - 1)))⁻¹) ^ (1 / p) * U)) +
        E * (m * ENNReal.ofReal T) ^ (1 / p)) := mul_le_mul' le_rfl h
    _ = (v⁻¹ * (ENNReal.ofReal ((3 * T) ^ β) *
          (2 * ((ENNReal.ofReal (T ^ (n - 1)))⁻¹) ^ (1 / p)))) * U +
        E * (v⁻¹ * (m * ENNReal.ofReal T) ^ (1 / p)) := by ring
    _ = _ := by rw [annular_time_rate hn hT, annular_time_mass_cancel hT hp]

end OAI.Analysis.Fourier.Restriction
