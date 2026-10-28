import OAI.Analysis.Normed.Function.Holder.Banach.Norm
import OAI.Analysis.Normed.Function.Holder.Banach.Maps
import Mathlib.Analysis.Real.Sqrt

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

/-- The elementary interpolation estimate between a uniform bound and an
α-Hölder bound, retaining the small uniform norm explicitly. -/
theorem half_holder_bound {X F : Type*} [PseudoMetricSpace X]
    [NormedAddCommGroup F] (f : X → F) {α A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h₀ : ∀ x y, ‖f x - f y‖ ≤ A)
    (hα : ∀ x y, ‖f x - f y‖ ≤ B * (dist x y) ^ α) :
    ∀ x y, ‖f x - f y‖ ≤ Real.sqrt (A * B) * (dist x y) ^ (α / 2) := by
  intro x y
  have hd : ((dist x y) ^ (α / 2)) ^ 2 = (dist x y) ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul dist_nonneg]
    congr 1
    ring
  have hs : (Real.sqrt (A * B)) ^ 2 = A * B := Real.sq_sqrt (mul_nonneg hA hB)
  have hsq : ‖f x - f y‖ ^ 2 ≤ A * (B * (dist x y) ^ α) := by
    simpa only [pow_two] using mul_le_mul (h₀ x y) (hα x y) (norm_nonneg _) hA
  have ht : 0 ≤ Real.sqrt (A * B) * (dist x y) ^ (α / 2) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg dist_nonneg _)
  have ht2 : (Real.sqrt (A * B) * (dist x y) ^ (α / 2)) ^ 2 =
      A * (B * (dist x y) ^ α) := by rw [mul_pow, hs, hd]; ring
  nlinarith

namespace HolderMap

variable {X F : Type*} [MetricSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {α : ℝ}

theorem value_half_holder (f : HolderMap X F α) :
    ∀ x y, ‖HolderMap.value f x - HolderMap.value f y‖ ≤
      Real.sqrt (2 * ‖HolderMap.value f‖ * ‖f‖) * (dist x y) ^ (α / 2) := by
  apply half_holder_bound (HolderMap.value f) (by positivity) (norm_nonneg f)
  · intro x y
    have hx := (HolderMap.value f).norm_coe_le_norm x
    have hy := (HolderMap.value f).norm_coe_le_norm y
    exact (_root_.norm_sub_le _ _).trans (by linarith)
  · exact HolderMap.norm_sub_le f

def lowerHalf (hα : 0 ≤ α) (f : HolderMap X F α) : HolderMap X F (α / 2) :=
  HolderMap.ofBounded (by positivity) (HolderMap.value f) (HolderMap.value_half_holder f)

@[simp] theorem value_lowerHalf (hα : 0 ≤ α) (f : HolderMap X F α) :
    HolderMap.value (HolderMap.lowerHalf hα f) = HolderMap.value f := rfl

theorem norm_lowerHalf_le (hα : 0 ≤ α) (f : HolderMap X F α) :
    ‖HolderMap.lowerHalf hα f‖ ≤ max ‖HolderMap.value f‖ (Real.sqrt (2 * ‖HolderMap.value f‖ * ‖f‖)) :=
  HolderMap.norm_ofBounded_le (by positivity) _ (Real.sqrt_nonneg _) (HolderMap.value_half_holder f)

theorem norm_lowerHalf_le_twice (hα : 0 ≤ α) (f : HolderMap X F α) :
    ‖HolderMap.lowerHalf hα f‖ ≤ 2 * ‖f‖ := by
  apply (HolderMap.norm_lowerHalf_le hα f).trans
  apply max_le
  · linarith [HolderMap.value_norm_le f, norm_nonneg f]
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith [HolderMap.value_norm_le f, norm_nonneg f]

def lowerHalfLinear (hα : 0 ≤ α) : HolderMap X F α →ₗ[ℝ] HolderMap X F (α / 2) where
  toFun := HolderMap.lowerHalf hα
  map_add' _ _ := HolderMap.value_injective rfl
  map_smul' _ _ := HolderMap.value_injective rfl

def lowerHalfCLM (hα : 0 ≤ α) : HolderMap X F α →L[ℝ] HolderMap X F (α / 2) :=
  (HolderMap.lowerHalfLinear hα).mkContinuous 2 (HolderMap.norm_lowerHalf_le_twice hα)

end HolderMap
end OAI.Analysis.Normed.Function.Holder
