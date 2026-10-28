import OAI.Analysis.Fourier.Restriction.Sparse.Cutoff
import OAI.Analysis.Fourier.Restriction.Translations

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal BigOperators
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

def sparsePiece {n : ℕ} (u : SchwartzMap (Space n) ℂ) (R : ℝ)
    (z : Space n) (f : Space n → ℂ) : Space n → ℂ :=
  (ball 0 R).indicator (fun x ↦ f (x + z) / u (R⁻¹ • x))

theorem measurable_sparsePiece {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (R : ℝ) (z : Space n) {f : Space n → ℂ} (hf : Measurable f) :
    Measurable (sparsePiece u R z f) := by
  apply Measurable.indicator _ measurableSet_ball
  exact (hf.comp (measurable_id.add_const z)).div (u.continuous.measurable.comp (by fun_prop))

theorem sparsePiece_support {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    (R : ℝ) (z : Space n) (f : Space n → ℂ) (x : Space n) (hx : R < ‖x‖) :
    sparsePiece u R z f x = 0 := by
  exact indicator_of_notMem (by simpa only [mem_ball, dist_zero_right, not_lt] using hx.le) _

theorem norm_sparsePiece_le {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (hu : ∀ x, ‖x‖ ≤ 1 → c ≤ ‖u x‖)
    (z : Space n) (f : Space n → ℂ) (x : Space n) :
    ‖sparsePiece u R z f x‖ ≤ c⁻¹ * ‖(ball 0 R).indicator (fun x ↦ f (x + z)) x‖ := by
  by_cases hx : x ∈ ball (0 : Space n) R
  · have hx' : ‖x‖ < R := by simpa only [mem_ball, dist_zero_right] using hx
    have hunit : ‖R⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
      exact (inv_mul_le_iff₀ hR).mpr (by linarith)
    have hux := hu _ hunit
    have hpos : 0 < ‖u (R⁻¹ • x)‖ := hc.trans_le hux
    rw [sparsePiece, indicator_of_mem hx, indicator_of_mem hx, norm_div, div_eq_mul_inv, mul_comm c⁻¹]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hc hux) (norm_nonneg _)
  · rw [sparsePiece, indicator_of_notMem hx, indicator_of_notMem hx, norm_zero, mul_zero]

theorem sparsePiece_recover {n : ℕ} (u : SchwartzMap (Space n) ℂ)
    {c R : ℝ} (hc : 0 < c) (hR : 0 < R) (hu : ∀ x, ‖x‖ ≤ 1 → c ≤ ‖u x‖)
    (z : Space n) (f : Space n → ℂ) (x : Space n) :
    sparsePiece u R z f (x - z) * u (R⁻¹ • (x - z)) = (ball z R).indicator f x := by
  by_cases hx : x ∈ ball z R
  · have hx' : x - z ∈ ball (0 : Space n) R := by
      simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hx
    have hunit : ‖R⁻¹ • (x - z)‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
      apply (inv_mul_le_iff₀ hR).mpr
      have hxnorm : ‖x - z‖ < R := by simpa only [mem_ball, dist_zero_right] using hx'
      simpa only [mul_one] using hxnorm.le
    have hne : u (R⁻¹ • (x - z)) ≠ 0 := norm_pos_iff.mp (hc.trans_le (hu _ hunit))
    rw [sparsePiece, indicator_of_mem hx', indicator_of_mem hx, sub_add_cancel,
      div_mul_cancel₀ _ hne]
  · have hx' : x - z ∉ ball (0 : Space n) R := by
      simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hx
    rw [sparsePiece, indicator_of_notMem hx', indicator_of_notMem hx, zero_mul]

end OAI.Analysis.Fourier.Restriction
