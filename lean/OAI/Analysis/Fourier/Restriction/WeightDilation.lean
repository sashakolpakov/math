import OAI.Analysis.Fourier.Restriction.SchwartzWeight
import OAI.Analysis.Fourier.BochnerRiesz.Dilation

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Filter
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem polynomial_weight_dilate_le {n : ℕ} (x : Space n) {R a : ℝ}
    (hR : 1 ≤ R) (ha : 0 ≤ a) :
    (1 + ‖R • x‖) ^ a ≤ R ^ a * (1 + ‖x‖) ^ a := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ R)]
  have H := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + R * ‖x‖)
    (show 1 + R * ‖x‖ ≤ R * (1 + ‖x‖) by nlinarith) ha
  rwa [Real.mul_rpow (by linarith : 0 ≤ R) (by positivity)] at H

theorem integrable_polynomial_weight_dilate {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {R a : ℝ} (hR : 1 ≤ R) (ha : 0 ≤ a) :
    Integrable (fun x : Space n ↦ ‖f x‖ * (1 + ‖R • x‖) ^ a) := by
  apply ((integrable_schwartz_polynomial_weight f ha).const_mul (R ^ a)).mono'
  · fun_prop
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ ‖f x‖ * (R ^ a * (1 + ‖x‖) ^ a) :=
      mul_le_mul_of_nonneg_left (polynomial_weight_dilate_le x hR ha) (norm_nonneg _)
    _ = _ := by ring

theorem integral_polynomial_weight_dilate_le {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {R a : ℝ} (hR : 1 ≤ R) (ha : 0 ≤ a) :
    (∫ x : Space n, ‖f x‖ * (1 + ‖R • x‖) ^ a) ≤
      R ^ a * ∫ x : Space n, ‖f x‖ * (1 + ‖x‖) ^ a := by
  rw [← integral_const_mul]
  apply integral_mono (integrable_polynomial_weight_dilate f hR ha)
    ((integrable_schwartz_polynomial_weight f ha).const_mul _)
  intro x
  calc
    _ ≤ ‖f x‖ * (R ^ a * (1 + ‖x‖) ^ a) :=
      mul_le_mul_of_nonneg_left (polynomial_weight_dilate_le x hR ha) (norm_nonneg _)
    _ = _ := by ring

theorem integral_dilated_schwartz_weight {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {R : ℝ} (hR : 0 < R) (a : ℝ) :
    (∫ x : Space n, ‖f (R⁻¹ • x)‖ * (1 + ‖x‖) ^ a) =
      R ^ n * ∫ x : Space n, ‖f x‖ * (1 + ‖R • x‖) ^ a := by
  have H := Measure.integral_comp_smul_of_nonneg (volume : Measure (Space n))
    (fun x : Space n ↦ ‖f (R⁻¹ • x)‖ * (1 + ‖x‖) ^ a) R (hR := hR.le)
  simp only [smul_smul, inv_mul_cancel₀ hR.ne', one_smul, Space,
    finrank_euclideanSpace_fin, smul_eq_mul] at H
  rw [H]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hR.ne'), one_mul]

theorem dilated_schwartz_weight_bound {n : ℕ} (f : SchwartzMap (Space n) ℂ)
    {R a : ℝ} (hR : 1 ≤ R) (ha : 0 ≤ a) :
    Integrable (fun x : Space n ↦ ‖f (R⁻¹ • x)‖ * (1 + ‖x‖) ^ a) ∧
    (∫ x : Space n, ‖f (R⁻¹ • x)‖ * (1 + ‖x‖) ^ a) ≤
      (R ^ n * R ^ a) * ∫ x : Space n, ‖f x‖ * (1 + ‖x‖) ^ a := by
  have hR0 : 0 < R := by linarith
  constructor
  · exact integrable_schwartz_polynomial_weight (OAI.Analysis.Fourier.BochnerRiesz.schwartzDilate R⁻¹ (inv_ne_zero hR0.ne') f) ha
  · rw [integral_dilated_schwartz_weight f hR0]
    calc
      _ ≤ R ^ n * (R ^ a * ∫ x : Space n, ‖f x‖ * (1 + ‖x‖) ^ a) :=
        mul_le_mul_of_nonneg_left (integral_polynomial_weight_dilate_le f hR ha) (by positivity)
      _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
