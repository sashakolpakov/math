import OAI.Analysis.Normed.Function.Holder.Banach.Construct
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Fixed smooth chart fields give genuine bounded Hölder fields on the
closed convex chart patch. -/

noncomputable section
open Set
open scoped BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_fixed_holder_on_compact_convex {S : Set E}
    (hS : IsCompact S) (hSc : Convex ℝ S)
    (hdiam : ∀ x ∈ S, ∀ y ∈ S, ‖x-y‖ ≤ 1)
    (f : E → F) (hf : ContDiff ℝ 1 f)
    {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ P : HolderMap S F α, ∀ x : S, OAI.Analysis.Normed.Function.Holder.HolderMap.value P x = f x := by
  obtain ⟨M₀, hM₀⟩ := hS.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨M₁, hM₁⟩ := hS.exists_bound_of_continuousOn
    (hf.continuous_fderiv one_ne_zero).continuousOn
  let M := max 0 (max M₀ M₁)
  have hM : 0 ≤ M := le_max_left _ _
  have h₀ : M₀ ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have h₁ : M₁ ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  let b : S →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f x) (hf.continuous.comp continuous_subtype_val) M
    (fun x => (hM₀ x x.property).trans h₀)
  have hh (x y : S) : ‖b x-b y‖ ≤ M*dist x y^α := by
    have hl : ‖f x-f y‖ ≤ M*‖(x:E)-(y:E)‖ :=
      hSc.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hf.differentiable one_ne_zero z)
        (fun z hz => (hM₁ z hz).trans h₁) y.property x.property
    have hp : ‖(x:E)-(y:E)‖ ≤ ‖(x:E)-(y:E)‖^α :=
      Real.self_le_rpow_of_le_one (norm_nonneg _) (hdiam x x.property y y.property) hα1
    exact hl.trans (by simpa only [Subtype.dist_eq, dist_eq_norm] using
      mul_le_mul_of_nonneg_left hp hM)
  exact ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα b hh, fun _ => rfl⟩

end OAI.Analysis.Normed.Function.Holder
