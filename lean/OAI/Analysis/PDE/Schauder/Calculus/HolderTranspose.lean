import OAI.Analysis.Normed.Function.Holder.Banach.Linear

open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Schauder

open OAI.Analysis.Normed.Function.Holder

variable {X Z F : Type*} [MetricSpace X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}

local instance transposeFunctionGroup : NormedAddCommGroup (Z →L[ℝ] F) := inferInstance
local instance transposeFunctionSpace : NormedSpace ℝ (Z →L[ℝ] F) := inferInstance
local instance transposeHolderGroup : NormedAddCommGroup (OAI.Analysis.Normed.Function.Holder.HolderMap X F α) := inferInstance
local instance transposeHolderSpace : NormedSpace ℝ (OAI.Analysis.Normed.Function.Holder.HolderMap X F α) := inferInstance
local instance transposeTargetGroup : NormedAddCommGroup (Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X F α) := inferInstance
local instance transposeTargetSpace : NormedSpace ℝ (Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X F α) := inferInstance

def holderTransposeLinear (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Z →L[ℝ] F) α) : Z →ₗ[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X F α where
  toFun z := OAI.Analysis.Normed.Function.Holder.HolderMap.map (ContinuousLinearMap.apply ℝ F z) A
  map_add' z w := by
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x).map_add z w
  map_smul' c z := by
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    exact (OAI.Analysis.Normed.Function.Holder.HolderMap.value A x).map_smul c z

theorem norm_holderTransposeLinear_le (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Z →L[ℝ] F) α) (z : Z) :
    ‖holderTransposeLinear A z‖ ≤ ‖A‖*‖z‖ := by
  apply (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_map_le _ A).trans
  rw [mul_comm ‖A‖]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg A)
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg z)
  intro L
  simpa only [ContinuousLinearMap.apply_apply,mul_comm] using L.le_opNorm z

def holderTranspose (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Z →L[ℝ] F) α) : Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X F α :=
  (holderTransposeLinear A).mkContinuous ‖A‖ (norm_holderTransposeLinear_le A)

@[simp] theorem value_holderTranspose (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Z →L[ℝ] F) α) (z : Z) (x : X) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (holderTranspose A z) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value A x z := rfl

def holderTransposeOperatorLinear :
    OAI.Analysis.Normed.Function.Holder.HolderMap X (Z →L[ℝ] F) α →ₗ[ℝ] (Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X F α) where
  toFun := holderTranspose
  map_add' A B := by
    ext z : 1
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    rfl
  map_smul' c A := by
    ext z : 1
    apply OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective
    apply BoundedContinuousFunction.ext
    intro x
    rfl

theorem norm_holderTranspose_le (A : OAI.Analysis.Normed.Function.Holder.HolderMap X (Z →L[ℝ] F) α) :
    ‖holderTranspose A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (norm_holderTransposeLinear_le A)

def holderTransposeCLM :
    OAI.Analysis.Normed.Function.Holder.HolderMap X (Z →L[ℝ] F) α →L[ℝ] (Z →L[ℝ] OAI.Analysis.Normed.Function.Holder.HolderMap X F α) :=
  holderTransposeOperatorLinear.mkContinuous 1 (by
    intro A
    rw [one_mul]
    exact norm_holderTranspose_le A)

end OAI.Analysis.PDE.Schauder
