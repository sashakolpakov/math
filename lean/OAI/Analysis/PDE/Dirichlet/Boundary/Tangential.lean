import OAI.Analysis.PDE.Dirichlet.Boundary.Coercivity

open Filter
open scoped Topology

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem second_fderiv_add {f g : E → ℝ} (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (x : E) : fderiv ℝ (fderiv ℝ (fun y ↦ f y + g y)) x =
      fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x := by
  have heq : fderiv ℝ (fun y ↦ f y + g y) = fun y ↦ fderiv ℝ f y + fderiv ℝ g y := by
    funext y
    exact fderiv_add (hf.differentiable (by norm_num) y) (hg.differentiable (by norm_num) y)
  rw [heq]
  exact fderiv_add ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)
    ((hg.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x)

theorem bilinear_abs_le (H : E →L[ℝ] E →L[ℝ] ℝ) (v w : E) :
    |H v w| ≤ ‖H‖ * ‖v‖ * ‖w‖ := by
  calc
    |H v w| = ‖H v w‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖H v‖ * ‖w‖ := (H v).le_opNorm w
    _ ≤ (‖H‖ * ‖v‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (H.le_opNorm v) (norm_nonneg w)

/-- The real tangent Hessian is bounded purely by the fixed boundary data and
the upper scalar barrier; no second derivative of the unknown occurs in the constant. -/
theorem boundary_tangent_hessian_bound [CompleteSpace E]
    {B₀ r u : E → ℝ} {x v w : E} {a A : ℝ}
    (hB₀ : ContDiff ℝ 2 B₀) (hr : ContDiff ℝ 2 r) (hu : ContDiff ℝ 2 u)
    (hrne : fderiv ℝ r x ≠ 0) (hzero : ∀ᶠ y in 𝓝 x, r y = r x → u y = 0)
    (hfactor : fderiv ℝ u x = a • fderiv ℝ r x)
    (ha : 0 ≤ a) (haA : a ≤ A) (hv : fderiv ℝ r x v = 0) (hw : fderiv ℝ r x w = 0) :
    |fderiv ℝ (fderiv ℝ (fun y ↦ B₀ y + u y)) x v w| ≤
      (‖fderiv ℝ (fderiv ℝ B₀) x‖ + A * ‖fderiv ℝ (fderiv ℝ r) x‖) * ‖v‖ * ‖w‖ := by
  rw [second_fderiv_add hB₀ hu]
  simp only [add_apply]
  rw [level_set_tangent_hessian hr hu hrne hzero hfactor hv hw]
  calc
    |fderiv ℝ (fderiv ℝ B₀) x v w + a * fderiv ℝ (fderiv ℝ r) x v w| ≤
        |fderiv ℝ (fderiv ℝ B₀) x v w| + |a * fderiv ℝ (fderiv ℝ r) x v w| := abs_add_le _ _
    _ = |fderiv ℝ (fderiv ℝ B₀) x v w| + a * |fderiv ℝ (fderiv ℝ r) x v w| := by
      rw [abs_mul, abs_of_nonneg ha]
    _ ≤ ‖fderiv ℝ (fderiv ℝ B₀) x‖ * ‖v‖ * ‖w‖ +
        a * (‖fderiv ℝ (fderiv ℝ r) x‖ * ‖v‖ * ‖w‖) :=
      add_le_add (bilinear_abs_le _ v w) (mul_le_mul_of_nonneg_left (bilinear_abs_le _ v w) ha)
    _ ≤ ‖fderiv ℝ (fderiv ℝ B₀) x‖ * ‖v‖ * ‖w‖ +
        A * (‖fderiv ℝ (fderiv ℝ r) x‖ * ‖v‖ * ‖w‖) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right haA (by positivity))
    _ = _ := by ring

end OAI.Analysis.PDE.Dirichlet
