import OAI.Analysis.PDE.Dirichlet.RegularDomainTrace

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance closedHigherFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance closedHigherFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance closedHigherSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedHigherSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedHigherThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedHigherThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedHigherFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedHigherFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance

omit [Nontrivial E] in
/-- Continuous derivative traces give C³ regularity on the entire closed
regular domain, including nonconvex boundary patches. -/
theorem contDiffOn_three_regular_sublevel_of_continuous_traces
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {f : E → F} {G : E → E →L[ℝ] F}
    {H : E → E →L[ℝ] E →L[ℝ] F}
    {T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] F}
    (hf : ContinuousOn f {x | r x ≤ 0}) (hG : ContinuousOn G {x | r x ≤ 0})
    (hH : ContinuousOn H {x | r x ≤ 0}) (hT : ContinuousOn T {x | r x ≤ 0})
    (hd₀ : ∀ x, r x < 0 → HasFDerivAt f (G x) x)
    (hd₁ : ∀ x, r x < 0 → HasFDerivAt G (H x) x)
    (hd₂ : ∀ x, r x < 0 → HasFDerivAt H (T x) x) :
    ContDiffOn ℝ 3 f {x | r x ≤ 0} := by
  have hH₁ : ContDiffOn ℝ 1 H {x | r x ≤ 0} :=
    contDiffOn_succ_of_derivative_field 0 (contDiffOn_zero.mpr hT)
      (fun x hx => hasFDerivWithinAt_regular_sublevel_of_continuous_trace hr hreg hH hT hd₂ hx)
  have hG₂ : ContDiffOn ℝ 2 G {x | r x ≤ 0} :=
    contDiffOn_succ_of_derivative_field 1 hH₁
      (fun x hx => hasFDerivWithinAt_regular_sublevel_of_continuous_trace hr hreg hG hH hd₁ hx)
  exact contDiffOn_succ_of_derivative_field 2 hG₂
    (fun x hx => hasFDerivWithinAt_regular_sublevel_of_continuous_trace hr hreg hf hG hd₀ hx)

omit [Nontrivial E] in
theorem contDiffOn_four_regular_sublevel_of_continuous_traces
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {f : E → F} {G : E → E →L[ℝ] F}
    {H : E → E →L[ℝ] E →L[ℝ] F}
    {T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] F}
    {Q : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F}
    (hf : ContinuousOn f {x | r x ≤ 0}) (hG : ContinuousOn G {x | r x ≤ 0})
    (hH : ContinuousOn H {x | r x ≤ 0}) (hT : ContinuousOn T {x | r x ≤ 0})
    (hQ : ContinuousOn Q {x | r x ≤ 0})
    (hd₀ : ∀ x, r x < 0 → HasFDerivAt f (G x) x)
    (hd₁ : ∀ x, r x < 0 → HasFDerivAt G (H x) x)
    (hd₂ : ∀ x, r x < 0 → HasFDerivAt H (T x) x)
    (hd₃ : ∀ x, r x < 0 → HasFDerivAt T (Q x) x) :
    ContDiffOn ℝ 4 f {x | r x ≤ 0} := by
  have hG₃ : ContDiffOn ℝ 3 G {x | r x ≤ 0} :=
    contDiffOn_three_regular_sublevel_of_continuous_traces hr hreg hG hH hT hQ hd₁ hd₂ hd₃
  exact contDiffOn_succ_of_derivative_field 3 hG₃
    (fun x hx => hasFDerivWithinAt_regular_sublevel_of_continuous_trace hr hreg hf hG hd₀ hx)

omit [Nontrivial E] in
/-- The closed third trace produced by compactness upgrades an actual
C² Hölder jet to C³ regularity up to its physical boundary. -/
theorem C2Holder.contDiffOn_three_closed_of_trace
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩD α)
    (hv : ContDiffOn ℝ 3 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) {x | r x < 0})
    (T : {x | r x ≤ 0} →ᵇ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F))
    (hT : ∀ x (hx : r x < 0), T ⟨x, hx.le⟩ =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)))) x) :
    ContDiffOn ℝ 3 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) {x | r x ≤ 0} := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  apply contDiffOn_three_regular_sublevel_of_continuous_traces hr hreg
    (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U))
    (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U))
    (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U))
    (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension T)
    (fun x hx => OAI.Analysis.Normed.Function.Holder.C2Holder.hasFDerivAt_value_extension U hx)
    (fun x hx => OAI.Analysis.Normed.Function.Holder.C2Holder.hasFDerivAt_first_extension U hx)
  intro x hx
  rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply T (x := x) hx.le, hT x hx]
  have he : OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U) =ᶠ[𝓝 x]
      fderiv ℝ (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U))) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U) (x := y) hy.le]
    exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ U hy).2.symm
  have hd := (((hv x hx).contDiffAt (hΩ.mem_nhds hx)).fderiv_right
    (m := 2) (by norm_num)).fderiv_right (m := 1) (by norm_num)
  exact (hd.differentiableAt (by norm_num)).hasFDerivAt.congr_of_eventuallyEq he

end OAI.Analysis.PDE.Dirichlet
