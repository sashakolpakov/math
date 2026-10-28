import OAI.Analysis.Normed.Function.Holder.Banach.Linear
import OAI.Analysis.Normed.Function.Holder.Banach.Operator
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped BoundedContinuousFunction ContDiff
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.HolderMap

variable {X F G H : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {α : ℝ}

local instance bilinearOperatorNormedGroup : NormedAddCommGroup (G →L[ℝ] H) := inferInstance
local instance bilinearOperatorNormedSpace : NormedSpace ℝ (G →L[ℝ] H) := inferInstance

def bilinear (hα : 0 ≤ α) (L : F →L[ℝ] G →L[ℝ] H)
    (f : HolderMap X F α) (g : HolderMap X G α) : HolderMap X H α :=
  HolderMap.action hα (HolderMap.map L f) g

@[simp] theorem value_bilinear (hα : 0 ≤ α) (L : F →L[ℝ] G →L[ℝ] H)
    (f : HolderMap X F α) (g : HolderMap X G α) (x : X) :
    HolderMap.value (HolderMap.bilinear hα L f g) x = L (HolderMap.value f x) (HolderMap.value g x) := rfl

theorem norm_bilinear_le (hα : 0 ≤ α) (L : F →L[ℝ] G →L[ℝ] H)
    (f : HolderMap X F α) (g : HolderMap X G α) :
    ‖HolderMap.bilinear hα L f g‖ ≤ (2 * ‖L‖) * ‖f‖ * ‖g‖ := by
  calc
    _ ≤ 2 * ‖HolderMap.map L f‖ * ‖g‖ := HolderMap.norm_action_le hα _ _
    _ ≤ 2 * (‖L‖ * ‖f‖) * ‖g‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (HolderMap.norm_map_le L f) (by norm_num))
        (norm_nonneg g)
    _ = _ := by ring

def bilinearLinear (hα : 0 ≤ α) (L : F →L[ℝ] G →L[ℝ] H) :
    HolderMap X F α →ₗ[ℝ] HolderMap X G α →ₗ[ℝ] HolderMap X H α where
  toFun f := HolderMap.actionLinear hα (HolderMap.map L f)
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    change L (HolderMap.value f x + HolderMap.value g x) (HolderMap.value h x) =
      L (HolderMap.value f x) (HolderMap.value h x) + L (HolderMap.value g x) (HolderMap.value h x)
    rw [map_add]
    rfl
  map_smul' c f := by
    apply LinearMap.ext
    intro h
    apply HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    change L (c • HolderMap.value f x) (HolderMap.value h x) = c • L (HolderMap.value f x) (HolderMap.value h x)
    rw [map_smul]
    rfl

def bilinearCLM (hα : 0 ≤ α) (L : F →L[ℝ] G →L[ℝ] H) :
    HolderMap X F α →L[ℝ] HolderMap X G α →L[ℝ] HolderMap X H α :=
  (HolderMap.bilinearLinear hα L).mkContinuous₂ (2 * ‖L‖) (HolderMap.norm_bilinear_le hα L)

@[simp] theorem value_bilinearCLM (hα : 0 ≤ α) (L : F →L[ℝ] G →L[ℝ] H)
    (f : HolderMap X F α) (g : HolderMap X G α) (x : X) :
    HolderMap.value (HolderMap.bilinearCLM hα L f g) x = L (HolderMap.value f x) (HolderMap.value g x) := rfl

/-- Polynomial operations on Hölder fields are smooth in the Banach norm. -/
theorem contDiff_bilinear (hα : 0 ≤ α) (L : F →L[ℝ] G →L[ℝ] H) (n : ℕ∞ω) :
    ContDiff ℝ n (fun p : HolderMap X F α × HolderMap X G α ↦ HolderMap.bilinear hα L p.1 p.2) :=
  (HolderMap.bilinearCLM hα L).isBoundedBilinearMap.contDiff

end OAI.Analysis.Normed.Function.Holder.HolderMap
