import OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogWeight
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic

/-! # Regularized Point Weight -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedPointWeight

noncomputable section

/-! Actual reciprocal-power point weights and their quantitative comparison on a shrinking coordinate ball. -/

open _root_.MeasureTheory _root_.Metric Set
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def regularizedPointWeight (m : ℕ) (ε : ℝ) (z : E) : ℝ :=
  ((ε + ‖z‖ ^ 2) ^ m)⁻¹

theorem regularizedPointWeight_continuous (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (regularizedPointWeight (E := E) m ε) := by
  have h := Real.continuous_exp.comp (RegularizedLogWeight.regularizedNegativeLog_smooth (0 : E) m hε).continuous
  simpa only [Function.comp_def, RegularizedLogWeight.regularizedNegativeLog_exp (0 : E) m hε, sub_zero,
    regularizedPointWeight] using! h

omit [InnerProductSpace ℝ E] in
theorem regularizedPointWeight_nonneg (m : ℕ) {ε : ℝ} (hε : 0 < ε) (z : E) :
    0 ≤ regularizedPointWeight m ε z :=
  inv_nonneg.mpr (pow_nonneg (add_nonneg hε.le (sq_nonneg ‖z‖)) m)

omit [InnerProductSpace ℝ E] in
theorem regularizedPointWeight_ball_bound (m : ℕ) {ε : ℝ} (hε : 0 < ε)
    {z : E} (hz : z ∈ ball (0 : E) (Real.sqrt ε)) (a : ℝ) (ha : 0 ≤ a) :
    a ≤ (2 * ε) ^ m * (regularizedPointWeight m ε z * a) := by
  have hz' : ‖z‖ < Real.sqrt ε := by simpa only [mem_ball, dist_zero_right] using hz
  have hz2 : ‖z‖ ^ 2 ≤ ε := by
    have hs := Real.sq_sqrt hε.le
    have hn := norm_nonneg z
    nlinarith [Real.sqrt_nonneg ε]
  have hq : 0 < ε + ‖z‖ ^ 2 := add_pos_of_pos_of_nonneg hε (sq_nonneg ‖z‖)
  have hp : (ε + ‖z‖ ^ 2) ^ m ≤ (2 * ε) ^ m :=
    pow_le_pow_left₀ hq.le (by linarith) m
  have hb := mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr (pow_nonneg hq.le m))
  rw [mul_inv_cancel₀ (pow_ne_zero m hq.ne')] at hb
  have hc := mul_le_mul_of_nonneg_right hb ha
  simpa only [one_mul, mul_assoc, regularizedPointWeight] using hc

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedPointWeight
