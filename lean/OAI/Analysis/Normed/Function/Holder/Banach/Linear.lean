import OAI.Analysis.Normed.Function.Holder.Banach.Maps
import Mathlib.Analysis.Normed.Operator.NormedSpace

open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.HolderMap

variable {X F G : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {α : ℝ}

/-- Postcomposition acts on both the value and the Hölder difference quotient. -/
def map (L : F →L[ℝ] G) (f : HolderMap X F α) : HolderMap X G α := by
  refine ⟨(L.compLeftContinuousBounded X f.val.1,
    L.compLeftContinuousBounded (DistinctPairs X) f.val.2), ?_⟩
  intro q
  change (dist q.val.1 q.val.2) ^ α • L (f.val.2 q) =
    L (f.val.1 q.val.1) - L (f.val.1 q.val.2)
  rw [← map_smul, f.property q, map_sub]

@[simp] theorem value_map (L : F →L[ℝ] G) (f : HolderMap X F α) (x : X) :
    HolderMap.value (HolderMap.map L f) x = L (HolderMap.value f x) := rfl

theorem norm_map_le (L : F →L[ℝ] G) (f : HolderMap X F α) : ‖HolderMap.map L f‖ ≤ ‖L‖ * ‖f‖ := by
  change max ‖L.compLeftContinuousBounded X f.val.1‖
    ‖L.compLeftContinuousBounded (DistinctPairs X) f.val.2‖ ≤ _
  apply max_le
  · apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg L) (norm_nonneg f))).mpr
    intro x
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (HolderMap.norm_value_le f x) (norm_nonneg L))
  · apply (BoundedContinuousFunction.norm_le (mul_nonneg (norm_nonneg L) (norm_nonneg f))).mpr
    intro q
    exact (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((f.val.2.norm_coe_le_norm q).trans (le_max_right _ _)) (norm_nonneg L))

def mapLinear (L : F →L[ℝ] G) : HolderMap X F α →ₗ[ℝ] HolderMap X G α where
  toFun := HolderMap.map L
  map_add' f g := by
    apply HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    exact map_add L _ _
  map_smul' c f := by
    apply HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    exact map_smul L _ _

def mapCLM (L : F →L[ℝ] G) : HolderMap X F α →L[ℝ] HolderMap X G α :=
  (HolderMap.mapLinear L).mkContinuous ‖L‖ (HolderMap.norm_map_le L)

@[simp] theorem value_mapCLM (L : F →L[ℝ] G) (f : HolderMap X F α) (x : X) :
    HolderMap.value (HolderMap.mapCLM L f) x = L (HolderMap.value f x) := rfl

end OAI.Analysis.Normed.Function.Holder.HolderMap
