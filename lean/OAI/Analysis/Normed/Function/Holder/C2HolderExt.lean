import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance extFirstDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance extFirstDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance extSecondDerivativeNormedGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance
local instance extSecondDerivativeNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstance

/-- If the interior is dense in the underlying closed domain, the jet is
uniquely determined by the function. There are no independent boundary jets. -/
theorem value_injective (hKΩ : K ⊆ closure Ω) :
    Function.Injective (C2Holder.value (F := F) (hΩK := hΩK) (α := α)) := by
  intro f g hfg
  have hG : EqOn (boundedZeroExtension (C2Holder.firstDerivative f))
      (boundedZeroExtension (C2Holder.firstDerivative g)) Ω := by
    intro x hx
    rw [← (C2Holder.hasFDerivAt_value_extension f hx).fderiv,
      ← (C2Holder.hasFDerivAt_value_extension g hx).fderiv, hfg]
  have hGK := hG.of_subset_closure
    (continuousOn_boundedZeroExtension (C2Holder.firstDerivative f))
    (continuousOn_boundedZeroExtension (C2Holder.firstDerivative g)) hΩK hKΩ
  have hGval : C2Holder.firstDerivative f = C2Holder.firstDerivative g := by
    apply BoundedContinuousFunction.ext
    intro x
    simpa only [boundedZeroExtension_apply _ x.property] using hGK x.property
  have hH : EqOn (boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative f))
      (boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative g)) Ω := by
    intro x hx
    rw [← (C2Holder.hasFDerivAt_first_extension f hx).fderiv,
      ← (C2Holder.hasFDerivAt_first_extension g hx).fderiv, hGval]
  have hHK := hH.of_subset_closure
    (continuousOn_boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative f))
    (continuousOn_boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative g)) hΩK hKΩ
  have hHval : C2Holder.secondDerivative f = C2Holder.secondDerivative g := by
    apply BoundedContinuousFunction.ext
    intro x
    simpa only [boundedZeroExtension_apply _ x.property] using hHK x.property
  apply Subtype.ext
  apply Prod.ext hfg
  apply Prod.ext hGval
  exact OAI.Analysis.Normed.Function.Holder.HolderMap.value_injective hHval

end OAI.Analysis.Normed.Function.Holder.C2Holder
