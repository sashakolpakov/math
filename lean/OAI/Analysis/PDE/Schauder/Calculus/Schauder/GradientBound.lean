import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HessianBound

/-! A genuine lower-order interpolation bound using the real mean-value theorem. -/

noncomputable section
open _root_.MeasureTheory Set Metric
namespace OAI.Analysis.PDE.Schauder

theorem gradient_bound_of_function_hessian_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : E → ℝ) (hu : ContDiff ℝ 2 u) {U K : ℝ} (hU : 0 ≤ U) (hK : 0 ≤ K)
    (hub : ∀ x, |u x| ≤ U) (hKb : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ K) :
    ∀ x, ‖fderiv ℝ u x‖ ≤ 2 * U + K := by
  have hu1 : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ u) := (hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hLip (x y : E) : ‖fderiv ℝ u y - fderiv ℝ u x‖ ≤ K * ‖y - x‖ :=
    (convex_univ : Convex ℝ (Set.univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun x _ => hD x) (fun x _ => hKb x) (mem_univ x) (mem_univ y)
  intro x
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  let g : E → ℝ := fun y => u y - fderiv ℝ u x y
  have hg : Differentiable ℝ g := hu1.sub (fderiv ℝ u x).differentiable
  have hgd (y : E) : fderiv ℝ g y = fderiv ℝ u y - fderiv ℝ u x := by
    exact ((hu1 y).hasFDerivAt.sub (fderiv ℝ u x).hasFDerivAt).fderiv
  have hgb (y : E) (hy : y ∈ closedBall x 1) : ‖fderiv ℝ g y‖ ≤ K := by
    rw [hgd]
    have hn : ‖y - x‖ ≤ 1 := by simpa only [mem_closedBall, dist_eq_norm] using hy
    exact (hLip x y).trans (by nlinarith)
  have hx : x ∈ closedBall x 1 := mem_closedBall_self (by norm_num)
  have hxv : x + v ∈ closedBall x 1 := by
    simp only [mem_closedBall, dist_eq_norm, add_sub_cancel_left, hv, le_refl]
  have hm := (convex_closedBall x (1 : ℝ)).norm_image_sub_le_of_norm_fderiv_le
    (fun y _ => hg y) hgb hx hxv
  have he : g (x + v) - g x = (u (x + v) - u x) - fderiv ℝ u x v := by
    dsimp [g]
    rw [map_add]
    ring
  rw [he, add_sub_cancel_left, hv, mul_one, Real.norm_eq_abs] at hm
  have hd : |u (x + v) - u x| ≤ 2 * U := (abs_sub _ _).trans (by linarith [hub (x + v), hub x])
  rw [Real.norm_eq_abs]
  have := abs_sub (u (x + v) - u x) ((u (x + v) - u x) - fderiv ℝ u x v)
  rw [sub_sub_cancel] at this
  linarith

end OAI.Analysis.PDE.Schauder
