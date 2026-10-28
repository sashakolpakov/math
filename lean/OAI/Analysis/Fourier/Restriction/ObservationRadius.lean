import OAI.Analysis.Fourier.Restriction.RateAlgebra

open _root_.MeasureTheory
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def restrictionObservationRadius (n : ℕ) (R : ℝ) : ℝ := (2 + Real.pi) * R ^ (n + 2)

theorem restrictionObservationRadius_bounds (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    2 ≤ restrictionObservationRadius n R ∧ 2 * R ≤ restrictionObservationRadius n R ∧
      Real.pi / 2 ≤ restrictionObservationRadius n R := by
  have h1 : 1 ≤ R ^ (n + 2) := one_le_pow₀ hR
  have h2 : R ≤ R ^ (n + 2) := by
    calc
      R = R ^ 1 := (pow_one R).symm
      _ ≤ _ := pow_le_pow_right₀ hR (by omega)
  have hpi := Real.pi_pos
  unfold restrictionObservationRadius
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem restrictionObservationRadius_error (n : ℕ) {R : ℝ} (hR : 1 ≤ R) :
    (1 + R ^ 2) / restrictionObservationRadius n R * R ^ n ≤ 1 := by
  have hT : 0 < restrictionObservationRadius n R := by
    have := (restrictionObservationRadius_bounds n hR).1
    linarith
  rw [div_mul_eq_mul_div, div_le_one hT]
  have h1 : R ^ n ≤ R ^ (n + 2) := pow_le_pow_right₀ hR (by omega)
  have h2 : R ^ 2 * R ^ n = R ^ (n + 2) := by rw [← pow_add]; congr 1; omega
  unfold restrictionObservationRadius
  have hpi := mul_nonneg Real.pi_pos.le (pow_nonneg (by linarith : 0 ≤ R) (n + 2))
  nlinarith

theorem restrictionObservationRadius_power (n : ℕ) {R : ℝ} (hR : 0 < R) (δ : ℝ) :
    restrictionObservationRadius n R ^ δ =
      (2 + Real.pi) ^ δ * R ^ (((n : ℝ) + 2) * δ) := by
  unfold restrictionObservationRadius
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
    ← Real.rpow_mul hR.le]
  norm_num

end OAI.Analysis.Fourier.Restriction
