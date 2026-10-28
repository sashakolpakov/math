import OAI.Analysis.PDE.Dirichlet.Closed.HigherRegularity

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

open OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance closedFourthRegFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance closedFourthRegFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance closedFourthRegSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedFourthRegSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedFourthRegThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedFourthRegThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedFourthRegFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedFourthRegFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance

omit [Nontrivial E] in
/-- A genuine C² Hölder jet, interior C⁴ regularity, and continuous closed
third/fourth derivative traces imply C⁴ regularity on the closed regular
domain. No differentiability of the zero extensions outside the domain is used. -/
theorem C2Holder.contDiffOn_four_closed_of_traces
    {r : E → ℝ} (hr : ContDiff ℝ 3 r)
    (hreg : ∀ x, r x = 0 → fderiv ℝ r x ≠ 0)
    {hΩD : {x | r x < 0} ⊆ {x | r x ≤ 0}} {α : ℝ}
    (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩD α)
    (hv : ContDiffOn ℝ 4 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) {x | r x < 0})
    (T : {x | r x ≤ 0} →ᵇ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F))
    (Q : {x | r x ≤ 0} →ᵇ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F))
    (hT : ∀ x (hx : r x < 0), T ⟨x, hx.le⟩ =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)))) x)
    (hQ : ∀ x (hx : r x < 0), Q ⟨x, hx.le⟩ =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U))))) x) :
    ContDiffOn ℝ 4 (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)) {x | r x ≤ 0} := by
  have hΩ : IsOpen {x | r x < 0} := isOpen_lt hr.continuous continuous_const
  apply contDiffOn_four_regular_sublevel_of_continuous_traces hr hreg
    (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U))
    (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U))
    (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U))
    (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension T) (OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension Q)
    (fun x hx => OAI.Analysis.Normed.Function.Holder.C2Holder.hasFDerivAt_value_extension U hx)
    (fun x hx => OAI.Analysis.Normed.Function.Holder.C2Holder.hasFDerivAt_first_extension U hx)
  · intro x hx
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply T (x := x) hx.le, hT x hx]
    have he : OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U) =ᶠ[𝓝 x]
        fderiv ℝ (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U))) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply (OAI.Analysis.Normed.Function.Holder.C2Holder.secondDerivative U) (x := y) hy.le]
      exact (OAI.Analysis.Normed.Function.Holder.C2Holder.genuine_derivatives hΩ U hy).2.symm
    have hd := (((hv x hx).contDiffAt (hΩ.mem_nhds hx)).fderiv_right
      (m := 3) (by norm_num)).fderiv_right (m := 2) (by norm_num)
    exact (hd.differentiableAt (by norm_num)).hasFDerivAt.congr_of_eventuallyEq he
  · intro x hx
    rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply Q (x := x) hx.le, hQ x hx]
    have he : OAI.Analysis.Normed.Function.Holder.boundedZeroExtension T =ᶠ[𝓝 x]
        fderiv ℝ (fderiv ℝ (fderiv ℝ (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)))) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      rw [OAI.Analysis.Normed.Function.Holder.boundedZeroExtension_apply T (x := y) hy.le]
      exact hT y hy
    have hd := ((((hv x hx).contDiffAt (hΩ.mem_nhds hx)).fderiv_right
      (m := 3) (by norm_num)).fderiv_right (m := 2) (by norm_num)).fderiv_right
        (m := 1) (by norm_num)
    exact (hd.differentiableAt (by norm_num)).hasFDerivAt.congr_of_eventuallyEq he

end OAI.Analysis.PDE.Dirichlet
