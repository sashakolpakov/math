import OAI.Analysis.PDE.Schauder.Calculus.Boundary.EvenExtension
import OAI.Analysis.Normed.Function.Holder.Banach.Construct

/-! Bounded Hölder extension of vector-valued halfspace data by normal folding. -/

noncomputable section
open Set InnerProductSpace
open scoped BoundedContinuousFunction
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ F] [FiniteDimensional ℝ E] in
theorem normalFold_holder (e : E) (he : ‖e‖ = 1) (f : E → F)
    {α H : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H)
    (hh : ∀ x, 0 ≤ inner ℝ e x → ∀ y, 0 ≤ inner ℝ e y →
      ‖f x - f y‖ ≤ H * ‖x - y‖ ^ α) (x y : E) :
    ‖f (normalFold e x) - f (normalFold e y)‖ ≤ H * ‖x - y‖ ^ α := by
  exact (hh _ (normalFold_nonneg e x he) _ (normalFold_nonneg e y he)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (normalFold_norm_sub_le e x y he) hα) hH)

omit [FiniteDimensional ℝ E] in
theorem exists_bounded_halfspace_holder_extension (e : E) (he : ‖e‖ = 1) (f : E → F)
    (hf : Continuous f) {α H M : ℝ} (hα : 0 ≤ α) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hbound : ∀ x, 0 ≤ inner ℝ e x → ‖f x‖ ≤ M)
    (hh : ∀ x, 0 ≤ inner ℝ e x → ∀ y, 0 ≤ inner ℝ e y →
      ‖f x - f y‖ ≤ H * ‖x - y‖ ^ α) :
    ∃ A : OAI.Analysis.Normed.Function.Holder.HolderMap E F α,
      (∀ x, 0 ≤ inner ℝ e x → OAI.Analysis.Normed.Function.Holder.HolderMap.value A x = f x) ∧
      ‖A‖ ≤ max M H := by
  have hsup : ∀ x, ‖f (normalFold e x)‖ ≤ M := fun x => hbound _ (normalFold_nonneg e x he)
  let V : E →ᵇ F := BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => f (normalFold e x)) (hf.comp (normalFold_lipschitz e he).continuous) M hsup
  have hV : ∀ x y, ‖V x - V y‖ ≤ H * (dist x y) ^ α := by
    intro x y
    simpa only [V, BoundedContinuousFunction.coe_ofNormedAddCommGroup, dist_eq_norm]
      using normalFold_holder e he f hα hH hh x y
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα V hV, ?_, ?_⟩
  · intro x hx
    change f (normalFold e x) = f x
    simp only [normalFold, ite_eq_left hx]
  · exact (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα V hH hV).trans
      (max_le_max (BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ hM hsup) le_rfl)

end OAI.Analysis.PDE.Schauder
