import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftTaylor
import OAI.Analysis.PDE.Schauder.Boundary.Jet.LiftHolder
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section
open Filter
open scoped Topology
namespace OAI.Analysis.PDE.Schauder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Identification of the second jet from the quantitative first-jet error.
This only uses the Hölder regularity of the prescribed boundary coefficient. -/
theorem hasFDerivAt_boundary_firstJet
    (ℓ : E →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) (g b : E → F)
    {α C H : ℝ} (hα : 0 < α) (hC : 0 ≤ C) (_ : 0 ≤ H)
    (hb : ∀ x y, ‖b x - b y‖ ≤ H * ‖x - y‖ ^ α)
    (herr : ∀ y, ‖g y - ℓ y • b y‖ ≤ C * |ℓ y| ^ (1 + α))
    {x : E} (hx : ℓ x = 0) :
    HasFDerivAt g (ℓ.smulRight (b x)) x := by
  have hgx : g x = 0 := by
    have ht := herr x
    rw [hx, zero_smul, sub_zero, abs_zero, Real.zero_rpow (by linarith : 1 + α ≠ 0), mul_zero] at ht
    exact norm_eq_zero.mp (le_antisymm ht (norm_nonneg _))
  apply hasFDerivAt_of_holder_remainder _ _ _ hα (C := C + H)
  filter_upwards with y
  have hl : |ℓ y| ≤ ‖y - x‖ := by
    simpa only [hx, sub_zero] using abs_linear_height_sub_le ℓ hℓ y x
  have hpow : |ℓ y| ^ (1 + α) ≤ ‖y - x‖ ^ (1 + α) :=
    Real.rpow_le_rpow (abs_nonneg _) hl (by linarith)
  have hp : ‖y - x‖ * ‖y - x‖ ^ α = ‖y - x‖ ^ (1 + α) := by
    by_cases hy : y = x
    · subst y
      simp [Real.zero_rpow hα.ne', Real.zero_rpow (by linarith : 1 + α ≠ 0)]
    · rw [Real.rpow_add (norm_pos_iff.mpr (sub_ne_zero.mpr hy)), Real.rpow_one]
  have he : g y - g x - (ℓ.smulRight (b x)) (y - x) =
      (g y - ℓ y • b y) + ℓ y • (b y - b x) := by
    simp only [hgx, sub_zero, ContinuousLinearMap.smulRight_apply, map_sub, hx, smul_sub, zero_smul]
    abel
  rw [he]
  calc
    _ ≤ ‖g y - ℓ y • b y‖ + ‖ℓ y • (b y - b x)‖ := norm_add_le _ _
    _ ≤ C * ‖y - x‖ ^ (1 + α) + ‖y - x‖ * (H * ‖y - x‖ ^ α) := by
      apply add_le_add ((herr y).trans (mul_le_mul_of_nonneg_left hpow hC))
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hl (hb y x) (norm_nonneg _) (norm_nonneg _)
    _ = (C + H) * ‖y - x‖ ^ (1 + α) := by
      rw [mul_left_comm ‖y - x‖ H, hp]
      ring

theorem contDiff_two_of_derivative_fields
    (f : E → F) (g : E → E →L[ℝ] F) (h : E → E →L[ℝ] E →L[ℝ] F)
    (hf : ∀ x, HasFDerivAt f (g x) x)
    (hg : ∀ x, HasFDerivAt g (h x) x) (hh : Continuous h) :
    ContDiff ℝ 2 f := by
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) f
  apply contDiff_succ_iff_fderiv.mpr
  refine ⟨fun x ↦ (hf x).differentiableAt, ?_, ?_⟩
  · intro hn
    norm_num at hn
  · have he : fderiv ℝ f = g := funext (fun x ↦ (hf x).fderiv)
    rw [he]
    exact contDiff_one_iff_hasFDerivAt.mpr ⟨h, hh, hg⟩

end OAI.Analysis.PDE.Schauder
