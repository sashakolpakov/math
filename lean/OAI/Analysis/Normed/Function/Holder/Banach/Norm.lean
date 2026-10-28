import OAI.Analysis.Normed.Function.Holder.Banach.Construct

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.HolderMap

theorem norm_le_of_bounds {X F : Type*} [MetricSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {α C : ℝ} (hα : 0 ≤ α) (hC : 0 ≤ C) (f : HolderMap X F α)
    (hv : ∀ x, ‖HolderMap.value f x‖ ≤ C)
    (hh : ∀ x y, ‖HolderMap.value f x - HolderMap.value f y‖ ≤ C * (dist x y) ^ α) : ‖f‖ ≤ C := by
  have heq : f = HolderMap.ofBounded hα (HolderMap.value f) hh := HolderMap.value_injective rfl
  have hb := HolderMap.norm_ofBounded_le hα (HolderMap.value f) hC hh
  rw [← heq] at hb
  exact hb.trans (max_le ((BoundedContinuousFunction.norm_le hC).mpr hv) le_rfl)

end OAI.Analysis.Normed.Function.Holder.HolderMap
