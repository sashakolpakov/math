import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Boundary differentiation of continuous jets.  Derivatives on the closed
domain are derived from their interior limits, not postulated separately. -/

noncomputable section
open Set Filter
open scoped Topology
namespace OAI.Analysis.PDE.Elliptic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuous_jet_hasFDerivWithinAt {S : Set E} (hS : IsOpen S) (hconv : Convex ℝ S)
    {f : E → F} {D : E → E →L[ℝ] F}
    (hf : ContinuousOn f (closure S)) (hD : ContinuousOn D (closure S))
    (hd : ∀ y ∈ S, HasFDerivAt f (D y) y) {x : E} (hx : x ∈ closure S) :
    HasFDerivWithinAt f (D x) (closure S) x := by
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt) hconv hS
    (fun y hy => (hf y hy).mono subset_closure)
  apply ((hD x hx).mono subset_closure).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hd y hy).fderiv.symm

/-- A continuous interior derivative has the correct tangential boundary
trace, proved by differentiating a curve in the closed domain. -/
theorem continuous_jet_boundary_trace {S : Set E} (hS : IsOpen S) (hconv : Convex ℝ S)
    {f : E → F} {D : E → E →L[ℝ] F}
    (hf : ContinuousOn f (closure S)) (hD : ContinuousOn D (closure S))
    (hd : ∀ y ∈ S, HasFDerivAt f (D y) y) {x v : E} (hx : x ∈ closure S)
    (hline : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ closure S)
    (hzero : ∀ᶠ t : ℝ in 𝓝 0, f (x + t • v) = f x) : D x v = 0 := by
  have hj := continuous_jet_hasFDerivWithinAt hS hconv hf hD hd hx
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hh : HasDerivAt (fun t : ℝ => f (x + t • v)) (D x v) 0 := by
    simpa only [zero_smul, add_zero, Function.comp_def] using
      hj.comp_hasDerivAt_of_eq 0 hl hline (by simp)
  exact hh.unique ((hasDerivAt_const (0 : ℝ) (f x)).congr_of_eventuallyEq hzero)

end OAI.Analysis.PDE.Elliptic
namespace OAI.Analysis.Normed.Function.Holder.C2Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω K S : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

local instance boundaryJetFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance boundaryJetFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance

/-- Genuine boundary derivative of a stored Banach jet after a smooth chart.
Only interior derivative compatibility from `C2Holder` is used. -/
theorem hasFDerivWithinAt_chart_value (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α)
    (hS : IsOpen S) (hconv : Convex ℝ S) {G : E → E} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {x : E} (hx : x ∈ closure S) :
    HasFDerivWithinAt (fun y => OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G y))
      ((OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U) (G x)).comp (fderiv ℝ G x))
      (closure S) x := by
  apply OAI.Analysis.PDE.Elliptic.continuous_jet_hasFDerivWithinAt hS hconv
    ((OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U)).comp hG.continuous.continuousOn hGK)
    (D := fun y => (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U) (G y)).comp (fderiv ℝ G y))
  · exact ((OAI.Analysis.Normed.Function.Holder.continuousOn_boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U)).comp
      hG.continuous.continuousOn hGK).clm_comp (hG.continuous_fderiv one_ne_zero).continuousOn
  · intro y hy
    exact (U.hasFDerivAt_value_extension (hGΩ hy)).comp y
      (hG.differentiable one_ne_zero y).hasFDerivAt
  · exact hx

/-- Zero boundary data forces the tangential component of the stored first
jet to vanish. This is valid even before any boundary C³ regularity exists. -/
theorem chart_tangential_trace_zero (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α)
    (hS : IsOpen S) (hconv : Convex ℝ S) {G : E → E} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {x v : E} (hx : x ∈ closure S)
    (hline : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ closure S)
    (hzero : ∀ᶠ t : ℝ in 𝓝 0,
      OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G (x + t • v)) = OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G x)) :
    OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U) (G x) (fderiv ℝ G x v) = 0 := by
  have hj := U.hasFDerivWithinAt_chart_value hS hconv hG hGK hGΩ hx
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hh : HasDerivAt
      (fun t : ℝ => OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G (x + t • v)))
      (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U) (G x) (fderiv ℝ G x v)) 0 := by
    simpa only [zero_smul, add_zero, Function.comp_def, ContinuousLinearMap.comp_apply] using
      hj.comp_hasDerivAt_of_eq 0 hl hline (by simp)
  exact hh.unique ((hasDerivAt_const (0 : ℝ)
    (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G x))).congr_of_eventuallyEq hzero)

/-- The same trace statement for nonzero prescribed boundary data. -/
theorem chart_tangential_trace_eq (U : OAI.Analysis.Normed.Function.Holder.C2Holder (F := F) hΩK α)
    (hS : IsOpen S) (hconv : Convex ℝ S) {G : E → E} (hG : ContDiff ℝ 1 G)
    (hGK : MapsTo G (closure S) K) (hGΩ : MapsTo G S Ω)
    {x v : E} (hx : x ∈ closure S) {B : E → F} (hB : DifferentiableAt ℝ B (G x))
    (hline : ∀ᶠ t : ℝ in 𝓝 0, x + t • v ∈ closure S)
    (htrace : ∀ᶠ t : ℝ in 𝓝 0,
      OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G (x + t • v)) = B (G (x + t • v))) :
    OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U) (G x) (fderiv ℝ G x v) =
      fderiv ℝ B (G x) (fderiv ℝ G x v) := by
  have hj := U.hasFDerivWithinAt_chart_value hS hconv hG hGK hGΩ hx
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hh : HasDerivAt
      (fun t : ℝ => OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.value U) (G (x + t • v)))
      (OAI.Analysis.Normed.Function.Holder.boundedZeroExtension (OAI.Analysis.Normed.Function.Holder.C2Holder.firstDerivative U) (G x) (fderiv ℝ G x v)) 0 := by
    simpa only [zero_smul, add_zero, Function.comp_def, ContinuousLinearMap.comp_apply] using
      hj.comp_hasDerivAt_of_eq 0 hl hline (by simp)
  have hg : HasDerivAt (fun t : ℝ => B (G (x + t • v)))
      (fderiv ℝ B (G x) (fderiv ℝ G x v)) 0 := by
    have hc := hB.hasFDerivAt.comp x (hG.differentiable one_ne_zero x).hasFDerivAt
    simpa only [zero_smul, add_zero, Function.comp_def, ContinuousLinearMap.comp_apply] using
      hc.comp_hasDerivAt_of_eq 0 hl (by simp)
  exact hh.unique (hg.congr_of_eventuallyEq htrace)

end OAI.Analysis.Normed.Function.Holder.C2Holder
