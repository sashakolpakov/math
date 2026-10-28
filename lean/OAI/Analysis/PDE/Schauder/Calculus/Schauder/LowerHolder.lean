import OAI.Analysis.PDE.Schauder.Calculus.Schauder.HolderPullback
import OAI.Analysis.PDE.Schauder.Calculus.Schauder.PoissonHolder

/-! Lower-order Hölder bounds used by the localized equation. -/

noncomputable section
open Set
namespace OAI.Analysis.PDE.Schauder

theorem holder_of_bounded_lipschitz
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    (f : E → F) {α U L : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hU : 0 ≤ U) (hL : 0 ≤ L) (hu : ∀ x, ‖f x‖ ≤ U)
    (hl : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖) :
    ∀ x y, ‖f x - f y‖ ≤ (L + 2 * U) * ‖x - y‖ ^ α := by
  intro x y
  by_cases hd : ‖x - y‖ ≤ 1
  · have hp := Real.self_le_rpow_of_le_one (norm_nonneg (x - y)) hd hα1
    calc
      _ ≤ L * ‖x - y‖ := hl x y
      _ ≤ L * ‖x - y‖ ^ α := mul_le_mul_of_nonneg_left hp hL
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)
  · have hp : 1 ≤ ‖x - y‖ ^ α := Real.one_le_rpow (le_of_not_ge hd) hα
    have hb : ‖f x - f y‖ ≤ 2 * U := (norm_sub_le _ _).trans (by linarith [hu x, hu y])
    calc
      _ ≤ 2 * U := hb
      _ ≤ 2 * U * ‖x - y‖ ^ α := by nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _)

theorem compact_C1_holder
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C > 0, (∀ x, ‖f x‖ ≤ C) ∧ (∀ x y, ‖f x - f y‖ ≤ C * ‖x - y‖ ^ α) := by
  obtain ⟨U, hu⟩ := hfc.exists_bound_of_continuous hf.continuous
  obtain ⟨L, hl⟩ := (hfc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous
    ((hf.fderiv_right (m := 0) (by norm_num)).continuous)
  have hU : 0 ≤ U := (norm_nonneg (f 0)).trans (hu 0)
  have hL : 0 ≤ L := (norm_nonneg (fderiv ℝ f 0)).trans (hl 0)
  have hLip : ∀ x y, ‖f x - f y‖ ≤ L * ‖x - y‖ := by
    intro x y
    exact (convex_univ : Convex ℝ (univ : Set E)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hf.differentiable one_ne_zero z) (fun z _ => hl z)
      (mem_univ y) (mem_univ x)
  refine ⟨L + 2 * U + 1, by positivity, ?_, ?_⟩
  · intro x
    exact (hu x).trans (by linarith)
  · intro x y
    exact (holder_of_bounded_lipschitz f hα hα1 hU hL hu hLip x y).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (norm_nonneg _) _))

end OAI.Analysis.PDE.Schauder
