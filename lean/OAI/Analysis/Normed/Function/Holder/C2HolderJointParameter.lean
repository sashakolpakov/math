import OAI.Analysis.Normed.Function.Holder.C2HolderJoint

/-! Every finite parameter derivative of a smooth stored-jet family retains joint C²
regularity in the parameter and physical variables. -/
noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.Normed.Function.Holder

variable {Z H : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

def parameterDirections (u : Z → H) : List Z → Z → H
  | [] => u
  | w :: ws => fun z => fderiv ℝ (parameterDirections u ws) z w

theorem contDiffOn_parameterDirections {U : Set Z} (hU : IsOpen U)
    (u : Z → H) (hu : ContDiffOn ℝ ∞ u U) (ws : List Z) :
    ContDiffOn ℝ ∞ (parameterDirections u ws) U := by
  induction ws with
  | nil => exact hu
  | cons w ws ih =>
    exact (ih.fderiv_of_isOpen hU (by simp)).clm_apply contDiffOn_const

variable {E F : Type*} [FiniteDimensional ℝ Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace C2Holder

theorem contDiffOn_joint_value_parameterDirections
    {U : Set Z} {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}
    (hU : IsOpen U) (hΩ : IsOpen Ω)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ ∞ u U) (ws : List Z) :
    ContDiffOn ℝ 2 (fun p : Z × E =>
      boundedZeroExtension (C2Holder.value (parameterDirections u ws p.1)) p.2) (U ×ˢ Ω) :=
  C2Holder.contDiffOn_joint_value_smooth hU hΩ (parameterDirections u ws)
    (contDiffOn_parameterDirections hU u hu ws)

end C2Holder
end OAI.Analysis.Normed.Function.Holder
