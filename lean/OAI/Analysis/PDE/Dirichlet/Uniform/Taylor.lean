import OAI.Analysis.PDE.Dirichlet.Boundary.Tangential
import OAI.Analysis.PDE.Dirichlet.Boundary.Taylor

open Set Metric

noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_le_quadratic_of_zero_jet_at {f : E → F} (hf : ContDiff ℝ 2 f)
    {x : E} (hfx : f x = 0) (hDx : fderiv ℝ f x = 0) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hbound : ∀ y ∈ closedBall x R, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C) :
    ∀ y ∈ closedBall x R, ‖f y‖ ≤ C * ‖y - x‖ ^ 2 := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hx : x ∈ closedBall x R := mem_closedBall_self hR
  have hgrad : ∀ y ∈ closedBall x R, ‖fderiv ℝ f y‖ ≤ C * ‖y - x‖ := by
    intro y hy
    simpa only [hDx, sub_zero] using
      (convex_closedBall x R).norm_image_sub_le_of_norm_fderiv_le
        (fun z _ ↦ hdDf z) hbound hx hy
  intro y hy
  have hyR : ‖y - x‖ ≤ R := by simpa only [mem_closedBall, dist_eq_norm] using hy
  have hgrad' : ∀ z ∈ closedBall x ‖y - x‖, ‖fderiv ℝ f z‖ ≤ C * ‖y - x‖ := by
    intro z hz
    have hzy : ‖z - x‖ ≤ ‖y - x‖ := by simpa only [mem_closedBall, dist_eq_norm] using hz
    have hzR : z ∈ closedBall x R := by simpa only [mem_closedBall, dist_eq_norm] using hzy.trans hyR
    exact (hgrad z hzR).trans (mul_le_mul_of_nonneg_left hzy hC)
  have hx' : x ∈ closedBall x ‖y - x‖ := mem_closedBall_self (norm_nonneg _)
  have hy' : y ∈ closedBall x ‖y - x‖ := by simp [mem_closedBall, dist_eq_norm]
  have h := (convex_closedBall x ‖y - x‖).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ ↦ hdf z) hgrad' hx' hy'
  simpa only [hfx, sub_zero, pow_two, mul_assoc] using h

theorem second_fderiv_const_smul {f : E → ℝ} (hf : ContDiff ℝ 2 f) (a : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ a • f y)) x = a • fderiv ℝ (fderiv ℝ f) x := by
  have hD : fderiv ℝ (fun y ↦ a • f y) = fun y ↦ a • fderiv ℝ f y := by
    funext y
    exact ((hf.differentiable (by norm_num) y).hasFDerivAt.const_smul a).fderiv
  rw [hD]
  exact (((hf.fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) x).hasFDerivAt.const_smul a).fderiv

/-- Quantitative level-set Taylor control with a prescribed common neighborhood. -/
theorem quadratic_level_set_bound_from_data {f r : E → ℝ} (hf : ContDiff ℝ 2 f)
    (hr : ContDiff ℝ 2 r) {x : E} {a A C D R : ℝ}
    (hfx : f x = 0) (hrx : r x = 0) (hDx : fderiv ℝ f x = a • fderiv ℝ r x)
    (hA : 0 ≤ A) (hC : 0 ≤ C) (hD : 0 ≤ D) (hR : 0 ≤ R) (ha : |a| ≤ A)
    (hfbound : ∀ y ∈ closedBall x R, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C)
    (hrbound : ∀ y ∈ closedBall x R, ‖fderiv ℝ (fderiv ℝ r) y‖ ≤ D) :
    ∀ y ∈ closedBall x R, r y = 0 → |f y| ≤ (C + A * D) * ‖y - x‖ ^ 2 := by
  let g : E → ℝ := fun y ↦ f y + (-a) • r y
  have hg : ContDiff ℝ 2 g := hf.add (hr.const_smul (-a))
  have hgx : g x = 0 := by simp [g, hfx, hrx]
  have hDgx : fderiv ℝ g x = 0 := by
    have hd : fderiv ℝ g x = fderiv ℝ f x + (-a) • fderiv ℝ r x :=
      ((hf.differentiable (by norm_num) x).hasFDerivAt.add
        ((hr.differentiable (by norm_num) x).hasFDerivAt.const_smul (-a))).fderiv
    rw [hd, hDx]
    simp
  have hgbound : ∀ y ∈ closedBall x R, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ C + A * D := by
    intro y hy
    change ‖fderiv ℝ (fderiv ℝ (fun y ↦ f y + (-a) • r y)) y‖ ≤ _
    rw [second_fderiv_add hf (hr.const_smul (-a)), second_fderiv_const_smul hr]
    calc
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) y‖ + ‖(-a) • fderiv ℝ (fderiv ℝ r) y‖ :=
        ContinuousLinearMap.opNorm_add_le _ _
      _ ≤ ‖fderiv ℝ (fderiv ℝ f) y‖ + |a| * ‖fderiv ℝ (fderiv ℝ r) y‖ := by
        apply add_le_add le_rfl
        simpa only [Real.norm_eq_abs, abs_neg] using
          ContinuousLinearMap.opNorm_smul_le (-a) (fderiv ℝ (fderiv ℝ r) y)
      _ ≤ C + A * D := add_le_add (hfbound y hy)
        (mul_le_mul ha (hrbound y hy) (ContinuousLinearMap.opNorm_nonneg _) hA)
  intro y hy hry
  have h := norm_le_quadratic_of_zero_jet_at hg hgx hDgx (by positivity) hR hgbound y hy
  simpa only [g, hry, smul_zero, add_zero, Real.norm_eq_abs] using h

end OAI.Analysis.PDE.Dirichlet
