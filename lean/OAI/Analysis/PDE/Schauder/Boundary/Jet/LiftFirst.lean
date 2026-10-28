import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftRegularization
import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftTaylor
import OAI.Analysis.PDE.Schauder.Calculus.Boundary.Reflection

noncomputable section
open _root_.MeasureTheory Set Metric Filter InnerProductSpace
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

def regularizedBoundaryLift {m : ℕ} (e : EuclideanSpace ℝ (Fin m))
    (h : EuclideanSpace ℝ (Fin m) → ℝ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (inner ℝ e x) ^ 2 / 2 * regularizedTrace h (inner ℝ e x) (normalProjection e x)

@[simp] theorem regularizedBoundaryLift_zero {m : ℕ}
    (e : EuclideanSpace ℝ (Fin m)) (h : EuclideanSpace ℝ (Fin m) → ℝ)
    {x : EuclideanSpace ℝ (Fin m)} (hx : inner ℝ e x = 0) :
    regularizedBoundaryLift e h x = 0 := by
  simp [regularizedBoundaryLift, hx]

theorem regularizedBoundaryLift_quadratic {m : ℕ} {α : ℝ}
    (e : EuclideanSpace ℝ (Fin m)) (he : ‖e‖ = 1)
    (h : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    {x : EuclideanSpace ℝ (Fin m)} (hx : inner ℝ e x = 0)
    (y : EuclideanSpace ℝ (Fin m)) :
    |regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h) y| ≤ ‖h‖ / 2 * ‖y - x‖ ^ 2 := by
  have hi : |inner ℝ e y| ≤ ‖y - x‖ := by
    simpa only [inner_sub_right, hx, sub_zero, he, one_mul] using
      abs_real_inner_le_norm e (y - x)
  have hi2 : (inner ℝ e y) ^ 2 ≤ ‖y - x‖ ^ 2 := by
    have hh := mul_le_mul hi hi (abs_nonneg (inner ℝ e y)) (norm_nonneg (y - x))
    nlinarith [sq_abs (inner ℝ e y)]
  change |(inner ℝ e y) ^ 2 / 2 * regularizedTrace _ _ _| ≤ _
  rw [abs_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
  calc
    _ ≤ ((inner ℝ e y) ^ 2 / 2) * ‖h‖ :=
      mul_le_mul_of_nonneg_left (norm_regularizedTrace_le h _ _)
        (div_nonneg (sq_nonneg _) (by norm_num))
    _ ≤ ‖h‖ / 2 * ‖y - x‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hi2 (norm_nonneg h)]

/-- The regularized lift has its prescribed zero first jet on the boundary,
despite the datum being only Hölder continuous. -/
theorem hasFDerivAt_regularizedBoundaryLift_boundary {m : ℕ} {α : ℝ}
    (e : EuclideanSpace ℝ (Fin m)) (he : ‖e‖ = 1)
    (h : OAI.Analysis.Normed.Function.Holder.HolderMap (EuclideanSpace ℝ (Fin m)) ℝ α)
    {x : EuclideanSpace ℝ (Fin m)} (hx : inner ℝ e x = 0) :
    HasFDerivAt (regularizedBoundaryLift e (OAI.Analysis.Normed.Function.Holder.HolderMap.value h))
      (0 : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) x := by
  apply hasFDerivAt_of_holder_remainder _ _ _ (α := 1) (C := ‖h‖ / 2) (by norm_num)
  filter_upwards with y
  simpa only [regularizedBoundaryLift_zero e _ hx, sub_zero, zero_apply,
    Real.norm_eq_abs, show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two] using
    regularizedBoundaryLift_quadratic e he h hx y

end OAI.Analysis.PDE.Schauder
