import OAI.Analysis.Normed.Function.Holder.C2HolderJointLinear
import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity
import OAI.Analysis.Normed.Function.Holder.C2HolderDirichlet

/-! Actual joint C² evaluation of a C² family in the complete stored-jet space. -/
noncomputable section
open Set
open scoped Topology ContDiff BoundedContinuousFunction
namespace OAI.Analysis.Normed.Function.Holder

variable {Z E F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set Z} {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance storedFirstJetGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance storedFirstJetSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance storedSecondJetGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance storedSecondJetSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance storedJetGroup : NormedAddCommGroup (C2Holder (F := F) hΩK α) := inferInstance
local instance storedJetSpace : NormedSpace ℝ (C2Holder (F := F) hΩK α) := inferInstance

namespace C2Holder

theorem contDiffOn_joint_value (hU : IsOpen U) (hΩ : IsOpen Ω)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ 2 (fun p : Z × E => boundedZeroExtension (C2Holder.value (u p.1)) p.2) (U ×ˢ Ω) := by
  exact joint_linear_bcf_contDiff_two hU hΩ hΩK
    (C2Holder.valueCLM (F := F) (hΩK := hΩK) (α := α))
    (C2Holder.firstDerivativeCLM (F := F) (hΩK := hΩK) (α := α))
    (C2Holder.secondDerivativeCLM (F := F) (hΩK := hΩK) (α := α))
    (fun v x hx => C2Holder.hasFDerivAt_value_extension v hx)
    (fun v x hx => C2Holder.hasFDerivAt_first_extension v hx) u hu

theorem hasFDerivAt_joint_value (hU : IsOpen U) (hΩ : IsOpen Ω)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ 1 u U)
    (p : Z × E) (hp : p ∈ U ×ˢ Ω) :
    HasFDerivAt (fun p : Z × E => boundedZeroExtension (C2Holder.value (u p.1)) p.2)
      (jointJetDerivative (C2Holder.valueCLM (F := F) (hΩK := hΩK) (α := α))
        (C2Holder.firstDerivativeCLM (F := F) (hΩK := hΩK) (α := α)) u p) p :=
  (joint_linear_bcf_contDiff_one hU hΩ hΩK
    (C2Holder.valueCLM (F := F) (hΩK := hΩK) (α := α))
    (C2Holder.firstDerivativeCLM (F := F) (hΩK := hΩK) (α := α))
    (fun v _ hx => C2Holder.hasFDerivAt_value_extension v hx) u hu).2 p hp

theorem fderiv_joint_value_apply (hU : IsOpen U) (hΩ : IsOpen Ω)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ 1 u U)
    (p : Z × E) (hp : p ∈ U ×ˢ Ω) (w : Z × E) :
    fderiv ℝ (fun p : Z × E => boundedZeroExtension (C2Holder.value (u p.1)) p.2) p w =
      boundedZeroExtension (C2Holder.value (fderiv ℝ u p.1 w.1)) p.2 +
        boundedZeroExtension (C2Holder.firstDerivative (u p.1)) p.2 w.2 := by
  rw [(C2Holder.hasFDerivAt_joint_value hU hΩ u hu p hp).fderiv,jointJetDerivative_apply]
  rfl

theorem contDiffOn_joint_value_smooth (hU : IsOpen U) (hΩ : IsOpen Ω)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ ∞ u U) :
    ContDiffOn ℝ 2 (fun p : Z × E => boundedZeroExtension (C2Holder.value (u p.1)) p.2) (U ×ˢ Ω) :=
  C2Holder.contDiffOn_joint_value hU hΩ u (hu.of_le (by simp))

theorem contDiffOn_joint_value_parameter_derivative (hU : IsOpen U) (hΩ : IsOpen Ω)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ ∞ u U) (w : Z) :
    ContDiffOn ℝ 2 (fun p : Z × E => boundedZeroExtension (C2Holder.value (fderiv ℝ u p.1 w)) p.2)
      (U ×ˢ Ω) := by
  exact C2Holder.contDiffOn_joint_value_smooth hU hΩ (fun z => fderiv ℝ u z w)
    ((hu.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const)

end C2Holder
end OAI.Analysis.Normed.Function.Holder
