import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Regularized Log Weight -/

namespace OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogWeight

noncomputable section

/-! Actual smooth regularized logarithmic point weights in the original finite-dimensional coordinate norm. -/

open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def regularizedNegativeLog (x : E) (m : ℕ) (ε : ℝ) (z : E) : ℝ :=
  -(m : ℝ) * Real.log (ε + ‖z - x‖ ^ 2)

theorem regularizedNegativeLog_smooth (x : E) (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ∞ (regularizedNegativeLog x m ε) := by
  exact contDiff_const.mul ((contDiff_const.add ((contDiff_id.sub contDiff_const).norm_sq (𝕜 := ℝ))).log
    (fun z => ne_of_gt (add_pos_of_pos_of_nonneg hε (sq_nonneg ‖z - x‖))))

omit [InnerProductSpace ℝ E] in
theorem regularizedNegativeLog_exp (x : E) (m : ℕ) {ε : ℝ} (hε : 0 < ε) (z : E) :
    Real.exp (regularizedNegativeLog x m ε z) = ((ε + ‖z - x‖ ^ 2) ^ m)⁻¹ := by
  rw [regularizedNegativeLog, neg_mul, Real.exp_neg, Real.exp_nat_mul,
    Real.exp_log (add_pos_of_pos_of_nonneg hε (sq_nonneg ‖z - x‖))]

end

end OAI.AlgebraicGeometry.DivisorClass.Chern.RegularizedLogWeight
