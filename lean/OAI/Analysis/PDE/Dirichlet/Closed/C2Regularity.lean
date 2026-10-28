import OAI.Analysis.PDE.Dirichlet.RegularDomainTrace

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance closedC2FirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance closedC2FirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance closedC2SecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedC2SecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance

omit [Nontrivial E] in
/-- The stored first and second derivatives are genuine one-sided
derivatives at every physical boundary point, not just interior jets. -/
theorem c2Holder_closed_derivative_fields
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩD α) {x : E} (hx : r x ≤ 0) :
    HasFDerivWithinAt (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U))
      (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U) x) {x | r x ≤ 0} x ∧
    HasFDerivWithinAt (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U))
      (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U) x) {x | r x ≤ 0} x := by
  constructor
  · exact hasFDerivWithinAt_regular_sublevel_of_continuous_trace hr hreg
      (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U))
      (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U))
      (fun y hy => OAI.Analysis.Normed.Function.Holder.C2Holder.hasFDerivAt_value_extension U hy) hx
  · exact hasFDerivWithinAt_regular_sublevel_of_continuous_trace hr hreg
      (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U))
      (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U))
      (fun y hy => OAI.Analysis.Normed.Function.Holder.C2Holder.hasFDerivAt_first_extension U hy) hx

omit [Nontrivial E] in
/-- Every actual C² Hölder Banach jet on a regular domain already gives
a C² function on its closed domain. No smooth representative is assumed. -/
theorem c2Holder_contDiffOn_two_closed
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩD α) :
    ContDiffOn ℝ 2 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) {x | r x ≤ 0} := by
  have hfirst : ContDiffOn ℝ 1 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U))
      {x | r x ≤ 0} :=
    contDiffOn_succ_of_derivative_field 0
      (contDiffOn_zero.mpr (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U)))
      (fun x hx => (c2Holder_closed_derivative_fields hr hreg U hx).2)
  exact contDiffOn_succ_of_derivative_field 1 hfirst
    (fun x hx => (c2Holder_closed_derivative_fields hr hreg U hx).1)

end OAI.Analysis.PDE.Dirichlet
