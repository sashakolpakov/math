import OAI.Analysis.PDE.Elliptic.Boundary.FlatRemainder

/-! Controlling every tangential row of a symmetric Hessian controls all
but its normal-normal coefficient, also for interior-to-boundary pairs. -/

noncomputable section
namespace OAI.Analysis.PDE.Elliptic

open InnerProductSpace
open OAI.Analysis.PDE.Dirichlet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem directional_fderiv_oscillation {u : E → ℝ} (hu : ContDiff ℝ 2 u)
    (x z e : E) :
    ‖fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) x - fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) z‖ ≤
      ‖fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z‖ * ‖e‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  have he : (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) x -
      fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) z) w =
      (fderiv ℝ (fderiv ℝ u) x - fderiv ℝ (fderiv ℝ u) z) w e := by
    simp only [sub_apply]
    rw [show fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) x w =
      fderiv ℝ (fderiv ℝ u) x w e from OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice hu w e x,
      show fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) z w =
      fderiv ℝ (fderiv ℝ u) z w e from OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice hu w e z]
  rw [he]
  exact (ContinuousLinearMap.le_opNorm₂ _ w e).trans_eq (by ring)

theorem normal_remainder_of_tangent_rows (H : E →L[ℝ] E) {ν : E}
    (hν : ‖ν‖ = 1) (hH : H.toLinearMap.IsSymmetric) {M : ℝ} (hM : 0 ≤ M)
    (hrow : ∀ e, ‖e‖ ≤ 1 → inner ℝ ν e = 0 → ∀ w,
      |inner ℝ (H w) e| ≤ M * ‖w‖) :
    ‖H - inner ℝ (H ν) ν • rankOne ℝ ν ν‖ ≤ 8 * M := by
  have hall (w e : E) (he : inner ℝ ν e = 0) :
      |inner ℝ (H w) e| ≤ (M * ‖w‖) * ‖e‖ := by
    exact linear_form_tangent_bound (innerSL ℝ (H w)) ν (hrow · · · w) e he
  have hh := normal_remainder_operator_norm H hν hH hM hM
    (fun w e _ he => hall w e he)
    (fun e he => by simpa only [hν, mul_one] using hall ν e he)
  nlinarith

theorem hessian_normal_remainder_of_tangent_differentials
    {u : E → ℝ} (hu : ContDiff ℝ 2 u) {ν x z : E} (hν : ‖ν‖ = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hrow : ∀ e, ‖e‖ ≤ 1 → inner ℝ ν e = 0 →
      ‖fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) x -
        fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) z‖ ≤ M) :
    let H := fderiv ℝ (gradient u) x - fderiv ℝ (gradient u) z
    ‖H - inner ℝ (H ν) ν • rankOne ℝ ν ν‖ ≤ 8 * M := by
  dsimp only
  let H := fderiv ℝ (gradient u) x - fderiv ℝ (gradient u) z
  have hH : H.toLinearMap.IsSymmetric :=
    (fderiv_gradient_isSymmetric hu x).sub (fderiv_gradient_isSymmetric hu z)
  apply normal_remainder_of_tangent_rows H hν hH hM
  intro e he hνe w
  have hid : inner ℝ (H w) e =
      (fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) x -
        fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) z) w := by
    simp only [H, sub_apply, inner_sub_left, inner_fderiv_gradient_at hu.contDiffAt]
    rw [show fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) x w =
      fderiv ℝ (fderiv ℝ u) x w e from OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice hu w e x,
      show fderiv ℝ (OAI.Analysis.PDE.Dirichlet.directionalDerivative u e) z w =
      fderiv ℝ (fderiv ℝ u) z w e from OAI.Analysis.PDE.Dirichlet.directionalDerivative_twice hu w e z]
  rw [hid]
  exact (ContinuousLinearMap.le_opNorm _ w).trans
    (mul_le_mul_of_nonneg_right (hrow e he hνe) (norm_nonneg _))

end OAI.Analysis.PDE.Elliptic
