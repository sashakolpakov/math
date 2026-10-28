import OAI.Analysis.Fourier.Restriction.BRFarField
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open OAI.Analysis.Fourier.Wave

open _root_.MeasureTheory Set Metric
open scoped ENNReal
noncomputable section
namespace OAI.Analysis.Fourier.Restriction

theorem eLpNorm_compact_eq_restrict {n : ℕ} {f : Space n → ℂ} {R : ℝ}
    (hs : ∀ x, R < ‖x‖ → f x = 0) (p : ℝ≥0∞) :
    eLpNorm f p volume = eLpNorm f p (volume.restrict (closedBall 0 R)) := by
  have he : (closedBall (0 : Space n) R).indicator f = f := by
    funext x
    by_cases hx : x ∈ closedBall (0 : Space n) R
    · simp only [indicator_of_mem hx]
    · rw [indicator_of_notMem hx, hs x (by simpa only [mem_closedBall, dist_zero_right, not_le] using hx)]
  rw [← eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall, he]

theorem integral_norm_le_compact_Lp {n : ℕ} {f : Space n → ℂ} {R p : ℝ}
    (hf : Integrable f) (hs : ∀ x, R < ‖x‖ → f x = 0) (hp : 1 ≤ p) :
    ENNReal.ofReal (∫ x, ‖f x‖) ≤ eLpNorm f (ENNReal.ofReal p) volume *
      volume (closedBall (0 : Space n) R) ^ (1 - 1 / p) := by
  have H := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (ENNReal.one_le_ofReal.mpr hp)
    (hf.aestronglyMeasurable.mono_measure
      (Measure.restrict_le_self (s := closedBall (0 : Space n) R)))
  rw [← eLpNorm_compact_eq_restrict hs 1,
    ← eLpNorm_compact_eq_restrict hs (ENNReal.ofReal p),
    Measure.restrict_apply_univ, ENNReal.toReal_one, ENNReal.toReal_ofReal (by linarith),
    div_one, eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm hf] at H
  exact H

theorem compact_ball_volume_factor {n : ℕ} {R p : ℝ} (hR : 1 ≤ R) (hp : 1 ≤ p) :
    volume (closedBall (0 : Space n) R) ^ (1 - 1 / p) ≤
      ENNReal.ofReal (R ^ n) * volume (ball (0 : Space n) 1) ^ (1 - 1 / p) := by
  have hs : 0 ≤ 1 - 1 / p := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp
    simpa only [div_one] using sub_nonneg.mpr this
  rw [Measure.addHaar_closedBall volume _ (by linarith : 0 ≤ R)]
  simp only [Space, finrank_euclideanSpace_fin]
  rw [ENNReal.mul_rpow_of_nonneg _ _ hs]
  apply mul_le_mul' _ le_rfl
  calc
    _ ≤ ENNReal.ofReal (R ^ n) ^ (1 : ℝ) :=
      ENNReal.rpow_le_rpow_of_exponent_le
        (ENNReal.one_le_ofReal.mpr (one_le_pow₀ hR)) (sub_le_self _ (by positivity))
    _ = _ := ENNReal.rpow_one _

theorem integral_norm_le_compact_Lp_polynomial {n : ℕ} {f : Space n → ℂ} {R p : ℝ}
    (hf : Integrable f) (hs : ∀ x, R < ‖x‖ → f x = 0) (hR : 1 ≤ R) (hp : 1 ≤ p) :
    ENNReal.ofReal (∫ x, ‖f x‖) ≤ ENNReal.ofReal (R ^ n) *
      volume (ball (0 : Space n) 1) ^ (1 - 1 / p) * eLpNorm f (ENNReal.ofReal p) volume := by
  calc
    _ ≤ eLpNorm f (ENNReal.ofReal p) volume * volume (closedBall (0 : Space n) R) ^ (1 - 1 / p) :=
      integral_norm_le_compact_Lp hf hs hp
    _ ≤ eLpNorm f (ENNReal.ofReal p) volume *
        (ENNReal.ofReal (R ^ n) * volume (ball (0 : Space n) 1) ^ (1 - 1 / p)) :=
      mul_le_mul' le_rfl (compact_ball_volume_factor hR hp)
    _ = _ := by ring

end OAI.Analysis.Fourier.Restriction
