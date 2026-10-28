import OAI.Analysis.Normed.Function.Holder.Banach.Construct

open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.HolderMap

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}

@[simp] theorem value_zero : HolderMap.value (0 : HolderMap X F α) = 0 := rfl
@[simp] theorem value_add (f g : HolderMap X F α) : HolderMap.value (f + g) = HolderMap.value f + HolderMap.value g := rfl
@[simp] theorem value_smul (c : ℝ) (f : HolderMap X F α) : HolderMap.value (c • f) = c • HolderMap.value f := rfl

def valueLinear : HolderMap X F α →ₗ[ℝ] (X →ᵇ F) where
  toFun := HolderMap.value
  map_add' := HolderMap.value_add
  map_smul' := HolderMap.value_smul

/-- Forgetting the Hölder seminorm is a norm-decreasing linear map. -/
def valueCLM : HolderMap X F α →L[ℝ] (X →ᵇ F) :=
  (HolderMap.valueLinear (X := X) (F := F) (α := α)).mkContinuous 1 (by
    intro f
    change ‖HolderMap.value f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using HolderMap.value_norm_le f)

@[simp] theorem valueCLM_apply (f : HolderMap X F α) : HolderMap.valueCLM f = HolderMap.value f := rfl

end OAI.Analysis.Normed.Function.Holder.HolderMap
