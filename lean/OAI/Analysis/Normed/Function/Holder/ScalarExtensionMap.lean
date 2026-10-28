import OAI.Analysis.Normed.Function.Holder.ScalarExtension
import OAI.Analysis.Normed.Function.Holder.Banach.Construct
import OAI.Analysis.PDE.Dirichlet.HolderCompactness

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

variable {X : Type*} [MetricSpace X] {K : Set X} [Nonempty K]

theorem continuous_boundedHolderExtension (f : K → ℝ) {B H α : ℝ}
    (hf : ∀ y, |f y| ≤ B) (hH : 0 ≤ H) (hα : 0 < α) (hα1 : α ≤ 1) :
    Continuous (boundedHolderExtension f B H α) := by
  have he := OAI.Analysis.PDE.Dirichlet.equicontinuous_of_uniform_holder
    (u := fun _ : Unit ↦ boundedHolderExtension f B H α) (C := H) hα (fun _ x y ↦ ?_)
  · exact he.continuous ()
  · simpa only [Real.norm_eq_abs] using boundedHolderExtension_holder f hf hH hα.le hα1 x y

/-- Bounded scalar Hölder data on any nonempty subset extend without
increasing the graph norm. The formula is retained for symmetry arguments. -/
theorem exists_scalar_holder_extension {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (f : HolderMap K ℝ α) :
    ∃ g : HolderMap X ℝ α, ‖g‖ ≤ ‖f‖ ∧
      (∀ x : X, OAI.Analysis.Normed.Function.Holder.HolderMap.value g x =
        boundedHolderExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) ‖f‖ ‖f‖ α x) ∧
      (∀ y : K, OAI.Analysis.Normed.Function.Holder.HolderMap.value g y = OAI.Analysis.Normed.Function.Holder.HolderMap.value f y) := by
  have hf (y : K) : |OAI.Analysis.Normed.Function.Holder.HolderMap.value f y| ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_value_le f y
  let u : X → ℝ := boundedHolderExtension (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) ‖f‖ ‖f‖ α
  have hu : Continuous u := continuous_boundedHolderExtension _ hf (norm_nonneg f) hα hα1
  have hb (x : X) : ‖u x‖ ≤ ‖f‖ := by
    simpa only [Real.norm_eq_abs] using
      boundedHolderExtension_bound _ (norm_nonneg f) hf (norm_nonneg f) x
  let v : X →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup u hu ‖f‖ hb
  have hh (x y : X) : ‖v x - v y‖ ≤ ‖f‖ * dist x y ^ α := by
    simpa only [v, BoundedContinuousFunction.coe_ofNormedAddCommGroup, Real.norm_eq_abs] using
      boundedHolderExtension_holder (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) hf (norm_nonneg f) hα.le hα1 x y
  refine ⟨OAI.Analysis.Normed.Function.Holder.HolderMap.ofBounded hα.le v hh, ?_, fun _ ↦ rfl, ?_⟩
  · apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_ofBounded_le hα.le v (norm_nonneg f) hh).trans
    apply max_le _ le_rfl
    exact BoundedContinuousFunction.norm_ofNormedAddCommGroup_le hu (norm_nonneg f) hb
  · intro y
    apply boundedHolderExtension_eq (OAI.Analysis.Normed.Function.Holder.HolderMap.value f) hf (norm_nonneg f) hα
    intro a b
    simpa only [Real.norm_eq_abs, Subtype.dist_eq] using OAI.Analysis.Normed.Function.Holder.HolderMap.norm_sub_le f a b

end OAI.Analysis.Normed.Function.Holder
