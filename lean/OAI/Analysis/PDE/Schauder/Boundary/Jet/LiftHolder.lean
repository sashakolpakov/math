import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section
open Set Metric
namespace OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem abs_linear_height_sub_le (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (x y : E) :
    |ℓ x - ℓ y| ≤ ‖x - y‖ := by
  rw [← map_sub, ← Real.norm_eq_abs]
  exact (ℓ.le_opNorm (x - y)).trans (by nlinarith [norm_nonneg (x - y)])

/-- A field with a Hölder boundary jet and the matching scale-invariant
derivative bound is globally Hölder, including pairs crossing the boundary. -/
theorem holder_of_boundary_jet_and_derivative
    (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (f b : E → F)
    {α A B C : ℝ} (hα : 0 < α) (hαone : α < 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (herr : ∀ x, ‖f x - b x‖ ≤ A * |ℓ x| ^ α)
    (htrace : ∀ x y, ‖b x - b y‖ ≤ B * ‖x - y‖ ^ α)
    (hdiff : ∀ x, ℓ x ≠ 0 → DifferentiableAt ℝ f x)
    (hder : ∀ x, ℓ x ≠ 0 → ‖fderiv ℝ f x‖ ≤ C * |ℓ x| ^ (α - 1))
    (x y : E) :
    ‖f x - f y‖ ≤ (C + A * ((2 : ℝ) ^ α + (3 : ℝ) ^ α) + B) * ‖x - y‖ ^ α := by
  by_cases hxy : x = y
  · subst y
    simp only [sub_self, norm_zero, Real.zero_rpow hα.ne', mul_zero, le_refl]
  let d := ‖x - y‖
  have hd : 0 < d := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hdα : 0 ≤ d ^ α := Real.rpow_nonneg hd.le _
  have hscale : 0 ≤ A * ((2 : ℝ) ^ α + (3 : ℝ) ^ α) + B :=
    add_nonneg (mul_nonneg hA (add_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Real.rpow_nonneg (by norm_num) _))) hB
  by_cases hnear : 2 * d < |ℓ x|
  · have hheight (z : E) (hz : z ∈ closedBall x d) : d < |ℓ z| := by
      have hz' : ‖x - z‖ ≤ d := by simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using hz
      have hl := abs_linear_height_sub_le ℓ hℓ x z
      have ht : |ℓ x| ≤ |ℓ x - ℓ z| + |ℓ z| := by
        simpa only [sub_add_cancel] using abs_add_le (ℓ x - ℓ z) (ℓ z)
      linarith
    have hne (z : E) (hz : z ∈ closedBall x d) : ℓ z ≠ 0 :=
      abs_pos.mp (hd.trans (hheight z hz))
    have hbnd (z : E) (hz : z ∈ closedBall x d) :
        ‖fderiv ℝ f z‖ ≤ C * d ^ (α - 1) := by
      apply (hder z (hne z hz)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.rpow_le_rpow_of_nonpos hd (hheight z hz).le (by linarith)
    have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ hdiff z (hne z hz)) hbnd (convex_closedBall x d)
      (mem_closedBall_self hd.le) (show y ∈ closedBall x d by simp [d, dist_eq_norm, norm_sub_rev])
    have hpow : d ^ (α - 1) * d = d ^ α := by
      rw [Real.rpow_sub_one hd.ne', div_mul_cancel₀ _ hd.ne']
    have hsmall : ‖f x - f y‖ ≤ C * d ^ α := by
      rw [norm_sub_rev (f y), norm_sub_rev y] at hmv
      change ‖f x - f y‖ ≤ C * d ^ (α - 1) * d at hmv
      simpa only [mul_assoc, hpow] using hmv
    exact hsmall.trans (mul_le_mul_of_nonneg_right (by linarith) hdα)
  · have hheightx : |ℓ x| ≤ 2 * d := le_of_not_gt hnear
    have hheighty : |ℓ y| ≤ 3 * d := by
      have hl := abs_linear_height_sub_le ℓ hℓ y x
      rw [norm_sub_rev y] at hl
      have ht : |ℓ y| ≤ |ℓ y - ℓ x| + |ℓ x| := by
        simpa only [sub_add_cancel] using abs_add_le (ℓ y - ℓ x) (ℓ x)
      linarith
    have hxpow := Real.rpow_le_rpow (abs_nonneg (ℓ x)) hheightx hα.le
    have hypow := Real.rpow_le_rpow (abs_nonneg (ℓ y)) hheighty hα.le
    rw [Real.mul_rpow (by norm_num) hd.le] at hxpow hypow
    have ht : ‖f x - f y‖ ≤ ‖f x - b x‖ + ‖b x - b y‖ + ‖f y - b y‖ := by
      calc
        _ ≤ ‖f x - b x‖ + ‖b x - f y‖ := by
          simpa only [dist_eq_norm] using dist_triangle (f x) (b x) (f y)
        _ ≤ _ := by
          have h := dist_triangle (b x) (b y) (f y)
          simp only [dist_eq_norm] at h
          rw [norm_sub_rev (b y)] at h
          linarith
    have hx := herr x
    have hy := herr y
    have hb := htrace x y
    have ha := mul_le_mul_of_nonneg_left hxpow hA
    have ha' := mul_le_mul_of_nonneg_left hypow hA
    change ‖f x - f y‖ ≤ (C + A * ((2 : ℝ) ^ α + (3 : ℝ) ^ α) + B) * d ^ α
    change ‖b x - b y‖ ≤ B * d ^ α at hb
    nlinarith [mul_nonneg hC hdα]

end OAI.Analysis.PDE.Schauder
