import OAI.Analysis.Normed.Function.Holder.C2HolderRegularity
import Mathlib.Analysis.Calculus.FDeriv.Extend

open Set Filter
open scoped Topology ContDiff
noncomputable section
namespace OAI.Analysis.PDE.Dirichlet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
local instance closedTraceFirstGroup : NormedAddCommGroup (E →L[ℝ] F) := inferInstance
local instance closedTraceFirstSpace : NormedSpace ℝ (E →L[ℝ] F) := inferInstance
local instance closedTraceSecondGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedTraceSecondSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedTraceThirdGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedTraceThirdSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedTraceFourthGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance
local instance closedTraceFourthSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F) := inferInstance

/-- Continuous traces of a function and its interior derivative give the
actual one-sided derivative on a closed convex patch. -/
theorem hasFDerivWithinAt_closure_of_continuous_trace
    {Ω : Set E} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    {f : E → F} {G : E → E →L[ℝ] F}
    (hf : ContinuousOn f (closure Ω)) (hG : ContinuousOn G (closure Ω))
    (hd : ∀ x ∈ Ω, HasFDerivAt f (G x) x)
    {x : E} (hx : x ∈ closure Ω) :
    HasFDerivWithinAt f (G x) (closure Ω) x := by
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt) hc hΩ
    (fun y hy => (hf y hy).mono subset_closure)
  have he : G =ᶠ[𝓝[Ω] x] fderiv ℝ f := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).fderiv.symm
  exact ((hG x hx).mono subset_closure).congr' he

/-- A specified one-sided derivative field suffices to bootstrap finite
regularity. No global extension or uniqueness of derivatives is assumed. -/
theorem contDiffOn_succ_of_derivative_field (n : ℕ) {S : Set E}
    {f : E → F} {G : E → E →L[ℝ] F}
    (hG : ContDiffOn ℝ n G S)
    (hd : ∀ x ∈ S, HasFDerivWithinAt f (G x) S x) :
    ContDiffOn ℝ (n+1) f S := by
  apply (contDiffOn_succ_iff_hasFDerivWithinAt (n := (n : ℕ∞ω)) (by simp)).mpr
  intro x hx
  rw [insert_eq_of_mem hx]
  exact ⟨S, self_mem_nhdsWithin, by simp, G, hd, hG⟩

/-- Third-order interior derivative identities and continuous closed
traces imply genuine C³ regularity on the closed patch. -/
theorem contDiffOn_three_closure_of_continuous_traces
    {Ω : Set E} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    {f : E → F} {G : E → E →L[ℝ] F}
    {H : E → E →L[ℝ] E →L[ℝ] F}
    {T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] F}
    (hf : ContinuousOn f (closure Ω)) (hG : ContinuousOn G (closure Ω))
    (hH : ContinuousOn H (closure Ω)) (hT : ContinuousOn T (closure Ω))
    (hd₀ : ∀ x ∈ Ω, HasFDerivAt f (G x) x)
    (hd₁ : ∀ x ∈ Ω, HasFDerivAt G (H x) x)
    (hd₂ : ∀ x ∈ Ω, HasFDerivAt H (T x) x) :
    ContDiffOn ℝ 3 f (closure Ω) := by
  have hH₁ : ContDiffOn ℝ 1 H (closure Ω) :=
    contDiffOn_succ_of_derivative_field 0 (contDiffOn_zero.mpr hT)
      (fun x hx => hasFDerivWithinAt_closure_of_continuous_trace hΩ hc hH hT hd₂ hx)
  have hG₂ : ContDiffOn ℝ 2 G (closure Ω) :=
    contDiffOn_succ_of_derivative_field 1 hH₁
      (fun x hx => hasFDerivWithinAt_closure_of_continuous_trace hΩ hc hG hH hd₁ hx)
  exact contDiffOn_succ_of_derivative_field 2 hG₂
    (fun x hx => hasFDerivWithinAt_closure_of_continuous_trace hΩ hc hf hG hd₀ hx)

/-- The same closed-patch bootstrap at fourth order. The top trace is
only assumed continuous, not differentiable off the physical domain. -/
theorem contDiffOn_four_closure_of_continuous_traces
    {Ω : Set E} (hΩ : IsOpen Ω) (hc : Convex ℝ Ω)
    {f : E → F} {G : E → E →L[ℝ] F}
    {H : E → E →L[ℝ] E →L[ℝ] F}
    {T : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] F}
    {Q : E → E →L[ℝ] E →L[ℝ] E →L[ℝ] E →L[ℝ] F}
    (hf : ContinuousOn f (closure Ω)) (hG : ContinuousOn G (closure Ω))
    (hH : ContinuousOn H (closure Ω)) (hT : ContinuousOn T (closure Ω))
    (hQ : ContinuousOn Q (closure Ω))
    (hd₀ : ∀ x ∈ Ω, HasFDerivAt f (G x) x)
    (hd₁ : ∀ x ∈ Ω, HasFDerivAt G (H x) x)
    (hd₂ : ∀ x ∈ Ω, HasFDerivAt H (T x) x)
    (hd₃ : ∀ x ∈ Ω, HasFDerivAt T (Q x) x) :
    ContDiffOn ℝ 4 f (closure Ω) := by
  have hG₃ : ContDiffOn ℝ 3 G (closure Ω) :=
    contDiffOn_three_closure_of_continuous_traces hΩ hc hG hH hT hQ hd₁ hd₂ hd₃
  exact contDiffOn_succ_of_derivative_field 3 hG₃
    (fun x hx => hasFDerivWithinAt_closure_of_continuous_trace hΩ hc hf hG hd₀ hx)

end OAI.Analysis.PDE.Dirichlet
