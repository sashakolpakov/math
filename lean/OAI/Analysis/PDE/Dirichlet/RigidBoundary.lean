import OAI.Analysis.PDE.Dirichlet.Boundary.Taylor

/-! Quadratic boundary vanishing of the adapted affine tangential field. -/

open Set Filter
open scoped Topology

namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the affine field is tangent to the defining level set to first order,
its derivative of the defining function vanishes quadratically on that level set.
The conclusion is derived from the actual derivatives, not a boundary chart. -/
theorem affineDerivative_quadratic_on_boundary
    {r : E → ℝ} (hr : ContDiff ℝ 3 r) (hr0 : r 0 = 0)
    (hr' : fderiv ℝ r 0 ≠ 0) (e : E) (A : E →L[ℝ] E)
    (he : fderiv ℝ r 0 e = 0)
    (hjet : ∀ w, fderiv ℝ r 0 w = 0 →
      fderiv ℝ r 0 (A w) + fderiv ℝ (fderiv ℝ r) 0 w e = 0) :
    ∃ C R : ℝ, 0 < C ∧ 0 < R ∧ ∀ x, ‖x‖ ≤ R → r x = 0 →
      |affineDerivative r e A x| ≤ C * ‖x‖ ^ 2 := by
  have hr2 : ContDiff ℝ 2 r := hr.of_le (by norm_num)
  have hX : ContDiff ℝ 2 (affineDerivative r e A) :=
    contDiff_affineDerivative hr (by norm_num) e A
  have hX0 : affineDerivative r e A 0 = 0 := by
    simpa only [affineDerivative, map_zero, add_zero] using he
  have hker : ∀ w, fderiv ℝ r 0 w = 0 →
      fderiv ℝ (affineDerivative r e A) 0 w = 0 := by
    intro w hw
    have hd := directionalDerivative_affineDerivative hr2 e A w 0
    simp only [directionalDerivative, map_zero, add_zero] at hd
    exact hd.trans (hjet w hw)
  obtain ⟨a, ha⟩ := linear_form_factor_of_kernel
    (fderiv ℝ (affineDerivative r e A) 0) (fderiv ℝ r 0) hr' hker
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    exists_quadratic_bound_on_level_set hX hr2 hX0 hr0 ha

end OAI.Analysis.PDE.Dirichlet
