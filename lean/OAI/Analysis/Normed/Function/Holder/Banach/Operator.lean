import OAI.Analysis.Normed.Function.Holder.Banach.Norm
import OAI.Analysis.Normed.Function.Holder.Banach.Maps
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.HolderMap

variable {X F G : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {α : ℝ}

local instance operatorNormedGroup : NormedAddCommGroup (F →L[ℝ] G) := inferInstance
local instance operatorNormedSpace : NormedSpace ℝ (F →L[ℝ] G) := inferInstance

/-- Pointwise application of a bounded Hölder operator field. -/
def actionValue (a : HolderMap X (F →L[ℝ] G) α) (f : HolderMap X F α) : X →ᵇ G :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x ↦ HolderMap.value a x (HolderMap.value f x))
    ((HolderMap.value a).continuous.clm_apply (HolderMap.value f).continuous) (‖a‖ * ‖f‖)
    (fun x ↦ ((HolderMap.value a x).le_opNorm (HolderMap.value f x)).trans
      (mul_le_mul (HolderMap.norm_value_le a x) (HolderMap.norm_value_le f x)
        (norm_nonneg _) (norm_nonneg _)))

theorem action_holder (a : HolderMap X (F →L[ℝ] G) α) (f : HolderMap X F α) (x y : X) :
    ‖HolderMap.actionValue a f x - HolderMap.actionValue a f y‖ ≤ (2 * ‖a‖ * ‖f‖) * (dist x y) ^ α := by
  have heq : HolderMap.value a x (HolderMap.value f x) - HolderMap.value a y (HolderMap.value f y) =
      (HolderMap.value a x - HolderMap.value a y) (HolderMap.value f x) + HolderMap.value a y (HolderMap.value f x - HolderMap.value f y) := by
    simp only [sub_apply, map_sub]
    abel
  change ‖HolderMap.value a x (HolderMap.value f x) - HolderMap.value a y (HolderMap.value f y)‖ ≤ _
  rw [heq]
  calc
    _ ≤ ‖(HolderMap.value a x - HolderMap.value a y) (HolderMap.value f x)‖ +
        ‖HolderMap.value a y (HolderMap.value f x - HolderMap.value f y)‖ := norm_add_le _ _
    _ ≤ ‖HolderMap.value a x - HolderMap.value a y‖ * ‖HolderMap.value f x‖ +
        ‖HolderMap.value a y‖ * ‖HolderMap.value f x - HolderMap.value f y‖ :=
      add_le_add ((HolderMap.value a x - HolderMap.value a y).le_opNorm _) ((HolderMap.value a y).le_opNorm _)
    _ ≤ (‖a‖ * (dist x y) ^ α) * ‖f‖ + ‖a‖ * (‖f‖ * (dist x y) ^ α) := by
      apply add_le_add
      · exact mul_le_mul (HolderMap.norm_sub_le a x y) (HolderMap.norm_value_le f x)
          (norm_nonneg _) (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg dist_nonneg _))
      · exact mul_le_mul (HolderMap.norm_value_le a y) (HolderMap.norm_sub_le f x y)
          (norm_nonneg _) (norm_nonneg _)
    _ = _ := by ring

def action (hα : 0 ≤ α) (a : HolderMap X (F →L[ℝ] G) α) (f : HolderMap X F α) :
    HolderMap X G α := HolderMap.ofBounded hα (HolderMap.actionValue a f) (HolderMap.action_holder a f)

@[simp] theorem value_action (hα : 0 ≤ α) (a : HolderMap X (F →L[ℝ] G) α)
    (f : HolderMap X F α) (x : X) : HolderMap.value (HolderMap.action hα a f) x = HolderMap.value a x (HolderMap.value f x) := rfl

theorem norm_action_le (hα : 0 ≤ α) (a : HolderMap X (F →L[ℝ] G) α)
    (f : HolderMap X F α) : ‖HolderMap.action hα a f‖ ≤ 2 * ‖a‖ * ‖f‖ := by
  apply HolderMap.norm_le_of_bounds hα (by positivity)
  · intro x
    change ‖HolderMap.value a x (HolderMap.value f x)‖ ≤ _
    calc
      _ ≤ ‖HolderMap.value a x‖ * ‖HolderMap.value f x‖ := (HolderMap.value a x).le_opNorm _
      _ ≤ ‖a‖ * ‖f‖ := mul_le_mul (HolderMap.norm_value_le a x) (HolderMap.norm_value_le f x)
        (norm_nonneg _) (norm_nonneg _)
      _ ≤ _ := by nlinarith [norm_nonneg a, norm_nonneg f, mul_nonneg (norm_nonneg a) (norm_nonneg f)]
  · exact HolderMap.action_holder a f

def actionLinear (hα : 0 ≤ α) (a : HolderMap X (F →L[ℝ] G) α) :
    HolderMap X F α →ₗ[ℝ] HolderMap X G α where
  toFun := HolderMap.action hα a
  map_add' f g := by
    apply HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    change HolderMap.value a x (HolderMap.value f x + HolderMap.value g x) = HolderMap.value a x (HolderMap.value f x) + HolderMap.value a x (HolderMap.value g x)
    exact map_add _ _ _
  map_smul' c f := by
    apply HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    change HolderMap.value a x (c • HolderMap.value f x) = c • HolderMap.value a x (HolderMap.value f x)
    exact map_smul _ _ _

/-- Hölder operator fields act boundedly on Hölder functions. -/
def actionCLM (hα : 0 ≤ α) (a : HolderMap X (F →L[ℝ] G) α) :
    HolderMap X F α →L[ℝ] HolderMap X G α :=
  (HolderMap.actionLinear hα a).mkContinuous (2 * ‖a‖) (HolderMap.norm_action_le hα a)

@[simp] theorem value_actionCLM (hα : 0 ≤ α) (a : HolderMap X (F →L[ℝ] G) α)
    (f : HolderMap X F α) (x : X) : HolderMap.value (HolderMap.actionCLM hα a f) x = HolderMap.value a x (HolderMap.value f x) := rfl

end OAI.Analysis.Normed.Function.Holder.HolderMap
