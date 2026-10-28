import OAI.Analysis.Normed.Function.Holder.C2HolderJointWithinLinear
import OAI.Analysis.Normed.Function.Holder.C2HolderJointParameter
import OAI.Analysis.PDE.Dirichlet.Closed.C2Regularity

/-! Actual joint C² regularity up to the boundary of a regular physical domain. -/
noncomputable section
open Set
open scoped ContDiff
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {Z E F : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {U : Set Z} {r : E → ℝ} {α : ℝ}
  {hΩK : {x | r x < 0} ⊆ {x | r x ≤ 0}}

local instance closedJointFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance closedJointFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance closedJointSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedJointSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedJointGroup : NormedAddCommGroup (C2Holder (F := F) hΩK α) := inferInstance
local instance closedJointSpace : NormedSpace ℝ (C2Holder (F := F) hΩK α) := inferInstance

omit [Nontrivial E] in
theorem contDiffOn_joint_value_closed (hU : IsOpen U) (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ 2 u U) :
    ContDiffOn ℝ 2 (fun p : Z × E => boundedZeroExtension (C2Holder.value (u p.1)) p.2)
      (U ×ˢ {x | r x ≤ 0}) := by
  exact joint_linear_bcf_contDiff_two_within hU (Subset.rfl)
    (C2Holder.valueCLM (F := F) (hΩK := hΩK) (α := α))
    (C2Holder.firstDerivativeCLM (F := F) (hΩK := hΩK) (α := α))
    (C2Holder.secondDerivativeCLM (F := F) (hΩK := hΩK) (α := α))
    (fun v x hx => (OAI.Analysis.PDE.Dirichlet.c2Holder_closed_derivative_fields hr hreg v hx).1)
    (fun v x hx => (OAI.Analysis.PDE.Dirichlet.c2Holder_closed_derivative_fields hr hreg v hx).2) u hu

omit [Nontrivial E] in
theorem hasFDerivWithinAt_joint_value_closed (hU : IsOpen U) (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ 1 u U)
    (p : Z × E) (hp : p ∈ U ×ˢ {x | r x ≤ 0}) :
    HasFDerivWithinAt (fun q : Z × E => boundedZeroExtension (C2Holder.value (u q.1)) q.2)
      (jointJetDerivative (C2Holder.valueCLM (F := F) (hΩK := hΩK) (α := α))
        (C2Holder.firstDerivativeCLM (F := F) (hΩK := hΩK) (α := α)) u p)
      (U ×ˢ {x | r x ≤ 0}) p :=
  (joint_linear_bcf_contDiff_one_within hU Subset.rfl
    (C2Holder.valueCLM (F := F) (hΩK := hΩK) (α := α))
    (C2Holder.firstDerivativeCLM (F := F) (hΩK := hΩK) (α := α))
    (fun v _ hx => (OAI.Analysis.PDE.Dirichlet.c2Holder_closed_derivative_fields hr hreg v hx).1) u hu).2 p hp

omit [Nontrivial E] in
theorem contDiffOn_joint_value_parameterDirections_closed
    (hU : IsOpen U) (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    (u : Z → C2Holder (F := F) hΩK α) (hu : ContDiffOn ℝ ∞ u U) (ws : List Z) :
    ContDiffOn ℝ 2 (fun p : Z × E =>
      boundedZeroExtension (C2Holder.value (parameterDirections u ws p.1)) p.2)
      (U ×ˢ {x | r x ≤ 0}) :=
  C2Holder.contDiffOn_joint_value_closed hU hr hreg (parameterDirections u ws)
    ((contDiffOn_parameterDirections hU u hu ws).of_le (by simp))

end OAI.Analysis.Normed.Function.Holder.C2Holder
