import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftCalculus
import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftSecond

noncomputable section
open Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem eq_boundary_of_scale_error (ℓ : E →L[ℝ] ℝ) (s b : E → ℝ)
    {α C : ℝ} (hα : 0 < α) (herr : ∀ y, |s y - b y| ≤ C * |ℓ y| ^ α)
    {x : E} (hx : ℓ x = 0) : s x = b x := by
  have he := herr x
  rw [hx, abs_zero, Real.zero_rpow hα.ne', mul_zero] at he
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))

omit [NormedSpace ℝ E] in
theorem holder_smul_fixed {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (b : E → ℝ) {α H : ℝ}
    (hb : ∀ x y, |b x - b y| ≤ H * ‖x - y‖ ^ α)
    (T : F) (hT : ‖T‖ ≤ 1) (x y : E) :
    ‖b x • T - b y • T‖ ≤ H * ‖x - y‖ ^ α := by
  rw [← sub_smul, norm_smul, Real.norm_eq_abs]
  calc
    _ ≤ |b x - b y| * 1 := mul_le_mul_of_nonneg_left hT (abs_nonneg _)
    _ ≤ _ := by simpa only [mul_one] using hb x y

theorem hasFDerivAt_quadraticLift_boundary
    (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (s : E → ℝ)
    {M : ℝ} (hM : 0 ≤ M) (hs : ∀ y, |s y| ≤ M)
    {x : E} (hx : ℓ x = 0) :
    HasFDerivAt (fun y ↦ (ℓ y) ^ 2 / 2 * s y) (0 : E →L[ℝ] ℝ) x := by
  apply hasFDerivAt_of_holder_remainder _ _ _ (α := 1) (C := M / 2) (by norm_num)
  filter_upwards with y
  have hl : |ℓ y| ≤ ‖y - x‖ := by
    simpa only [hx, sub_zero] using abs_linear_height_sub_le ℓ hℓ y x
  have hsquare : (ℓ y) ^ 2 ≤ ‖y - x‖ ^ 2 := by
    have hh := mul_le_mul hl hl (abs_nonneg (ℓ y)) (norm_nonneg (y - x))
    nlinarith [sq_abs (ℓ y)]
  have hq : 0 ≤ (ℓ y) ^ 2 / 2 := div_nonneg (sq_nonneg _) (by norm_num)
  simp only [hx, zero_pow (by norm_num : 2 ≠ 0), zero_div, zero_mul, sub_zero,
    zero_apply, Real.norm_eq_abs, show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two,
    abs_mul, abs_of_nonneg hq]
  have hmul := mul_le_mul_of_nonneg_left (hs y) hq
  have hmul' := mul_le_mul_of_nonneg_right hsquare hM
  nlinarith

end OAI.Analysis.PDE.Schauder
