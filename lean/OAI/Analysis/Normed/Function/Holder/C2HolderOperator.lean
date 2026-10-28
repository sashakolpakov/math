import OAI.Analysis.Normed.Function.Holder.C2HolderDirichlet
import OAI.Analysis.Normed.Function.Holder.Banach.Operator

open Set
open scoped BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance operatorFirstDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance operatorFirstDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance operatorSecondDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance operatorSecondDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance coefficientNormedGroup :
    NormedAddCommGroup ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) := inferInstance
local instance coefficientNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) := inferInstance

/-- The Hessian projection retains its full Hölder norm. -/
def hessianCLM : C2Holder (F := F) hΩK α →L[ℝ] HolderMap K (E →L[ℝ] E →L[ℝ] F) α where
  toFun f := f.val.2.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := continuous_snd.snd.comp continuous_subtype_val

theorem norm_hessianCLM_apply_le (f : C2Holder (F := F) hΩK α) :
    ‖C2Holder.hessianCLM f‖ ≤ ‖f‖ := (le_max_right _ _).trans (le_max_right _ _)

/-- A second-order operator with Cα coefficients acts boundedly from C²,α to Cα. -/
def secondOrderCLM (hα : 0 ≤ α)
    (a : HolderMap K ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) α) :
    C2Holder (F := F) hΩK α →L[ℝ] HolderMap K G α :=
  (OAI.Analysis.Normed.Function.Holder.HolderMap.actionCLM hα a).comp C2Holder.hessianCLM

@[simp] theorem secondOrderCLM_apply (hα : 0 ≤ α)
    (a : HolderMap K ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) α)
    (f : C2Holder (F := F) hΩK α) (x : K) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C2Holder.secondOrderCLM hα a f) x = OAI.Analysis.Normed.Function.Holder.HolderMap.value a x (C2Holder.secondDerivative f x) := rfl

theorem norm_secondOrderCLM_apply_le (hα : 0 ≤ α)
    (a : HolderMap K ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) α)
    (f : C2Holder (F := F) hΩK α) :
    ‖C2Holder.secondOrderCLM hα a f‖ ≤ (2 * ‖a‖) * ‖f‖ :=
  (OAI.Analysis.Normed.Function.Holder.HolderMap.norm_action_le hα a (C2Holder.hessianCLM f)).trans
    (mul_le_mul_of_nonneg_left (C2Holder.norm_hessianCLM_apply_le f) (by positivity))

/-- On the open domain this is the differential operator applied to the actual
second Fréchet derivative, not an independent jet field. -/
theorem secondOrderCLM_eq_fderiv (hΩ : IsOpen Ω) (hα : 0 ≤ α)
    (a : HolderMap K ((E →L[ℝ] E →L[ℝ] F) →L[ℝ] G) α)
    (f : C2Holder (F := F) hΩK α) {x : E} (hx : x ∈ Ω) :
    OAI.Analysis.Normed.Function.Holder.HolderMap.value (C2Holder.secondOrderCLM hα a f) ⟨x, hΩK hx⟩ =
      OAI.Analysis.Normed.Function.Holder.HolderMap.value a ⟨x, hΩK hx⟩
        (fderiv ℝ (fderiv ℝ (boundedZeroExtension (C2Holder.value f))) x) := by
  rw [C2Holder.secondOrderCLM_apply, (C2Holder.genuine_derivatives hΩ f hx).2]

end OAI.Analysis.Normed.Function.Holder.C2Holder
