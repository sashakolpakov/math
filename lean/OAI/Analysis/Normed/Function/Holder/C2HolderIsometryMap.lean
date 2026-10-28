import OAI.Analysis.Normed.Function.Holder.C2HolderIsometry

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {α : ℝ}

local instance pullbackFirstENormedGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance
local instance pullbackFirstENormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance
local instance pullbackSecondENormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  inferInstance
local instance pullbackSecondENormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
local instance pullbackFirstFNormedGroup : NormedAddCommGroup (F →L[ℝ] ℝ) := inferInstance
local instance pullbackFirstFNormedSpace : NormedSpace ℝ (F →L[ℝ] ℝ) := inferInstance
local instance pullbackSecondFNormedGroup : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ) :=
  inferInstance
local instance pullbackSecondFNormedSpace : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ) := inferInstance

local instance pullbackFullENormedGroup : NormedAddCommGroup (FullSpaceC2 E α) := inferInstance
local instance pullbackFullENormedSpace : NormedSpace ℝ (FullSpaceC2 E α) := inferInstance
local instance pullbackFullFNormedGroup : NormedAddCommGroup (FullSpaceC2 F α) := inferInstance
local instance pullbackFullFNormedSpace : NormedSpace ℝ (FullSpaceC2 F α) := inferInstance
local instance pullbackFullEModule : Module ℝ (FullSpaceC2 E α) := inferInstance
local instance pullbackFullFModule : Module ℝ (FullSpaceC2 F α) := inferInstance
local instance pullbackFullESMul : SMul ℝ (FullSpaceC2 E α) := pullbackFullEModule.toSMul
local instance pullbackFullFSMul : SMul ℝ (FullSpaceC2 F α) := pullbackFullFModule.toSMul

def fullSpacePullback (hα : 0 ≤ α) (e : E ≃ₗᵢ[ℝ] F) (u : FullSpaceC2 F α) : FullSpaceC2 E α :=
  (exists_fullSpace_pullback hα e u).choose

@[simp] theorem fullSpacePullback_apply (hα : 0 ≤ α) (e : E ≃ₗᵢ[ℝ] F)
    (u : FullSpaceC2 F α) (x : E) :
    fullValue (fullSpacePullback hα e u) x = fullValue u (e x) :=
  congrFun (exists_fullSpace_pullback hα e u).choose_spec.1 x

theorem norm_fullSpacePullback_le (hα : 0 ≤ α) (e : E ≃ₗᵢ[ℝ] F) (u : FullSpaceC2 F α) :
    ‖fullSpacePullback hα e u‖ ≤ ‖u‖ :=
  (exists_fullSpace_pullback hα e u).choose_spec.2

def fullSpacePullbackLinear (hα : 0 ≤ α) (e : E ≃ₗᵢ[ℝ] F) :
    FullSpaceC2 F α →ₗ[ℝ] FullSpaceC2 E α where
  toFun := fullSpacePullback hα e
  map_add' u v := by
    apply OAI.Analysis.Normed.Function.Holder.C2Holder.value_injective (by simp)
    apply BoundedContinuousFunction.ext
    intro x
    change fullValue (fullSpacePullback hα e (u + v)) x =
      fullValue (fullSpacePullback hα e u) x + fullValue (fullSpacePullback hα e v) x
    rw [fullSpacePullback_apply, fullSpacePullback_apply, fullSpacePullback_apply]
    rfl
  map_smul' c u := by
    apply OAI.Analysis.Normed.Function.Holder.C2Holder.value_injective (by simp)
    apply BoundedContinuousFunction.ext
    intro x
    change fullValue (fullSpacePullback hα e (c • u)) x =
      c • fullValue (fullSpacePullback hα e u) x
    rw [fullSpacePullback_apply, fullSpacePullback_apply]
    rfl

/-- A coordinate isometry transports the actual Hölder solution space by a
bounded linear map of norm at most one. -/
def fullSpacePullbackCLM (hα : 0 ≤ α) (e : E ≃ₗᵢ[ℝ] F) :
    FullSpaceC2 F α →L[ℝ] FullSpaceC2 E α :=
  (fullSpacePullbackLinear hα e).mkContinuous 1
    (fun u ↦ by
      change ‖fullSpacePullback hα e u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_fullSpacePullback_le hα e u)

@[simp] theorem fullSpacePullbackCLM_apply (hα : 0 ≤ α) (e : E ≃ₗᵢ[ℝ] F)
    (u : FullSpaceC2 F α) (x : E) :
    fullValue (fullSpacePullbackCLM hα e u) x = fullValue u (e x) :=
  fullSpacePullback_apply hα e u x

end OAI.Analysis.Normed.Function.Holder
