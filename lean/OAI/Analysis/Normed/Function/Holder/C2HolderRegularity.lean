import OAI.Analysis.Normed.Function.Holder.C2HolderBanach

open Set Filter
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OAI.Analysis.Normed.Function.Holder

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
theorem continuousOn_boundedZeroExtension {K : Set E} (f : K →ᵇ F) :
    ContinuousOn (boundedZeroExtension f) K := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have heq : (fun x : K ↦ boundedZeroExtension f x) = fun x ↦ f x := by
    funext x
    exact boundedZeroExtension_apply f x.property
  change Continuous (fun x : K ↦ boundedZeroExtension f x)
  rw [heq]
  exact f.continuous

theorem contDiffOn_two_of_derivative_fields {Ω : Set E} (hΩ : IsOpen Ω)
    {v : E → F} {G : E → E →L[ℝ] F} {H : E → E →L[ℝ] E →L[ℝ] F}
    (hv : ∀ x ∈ Ω, HasFDerivAt v (G x) x)
    (hG : ∀ x ∈ Ω, HasFDerivAt G (H x) x)
    (hH : ContinuousOn H Ω) : ContDiffOn ℝ 2 v Ω := by
  have hGcont : ContDiffOn ℝ 1 G Ω := by
    change ContDiffOn ℝ (0 + 1) G Ω
    rw [contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
    refine ⟨fun x hx ↦ (hG x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    rw [contDiffOn_zero]
    exact hH.congr (fun x hx ↦ (hG x hx).fderiv)
  change ContDiffOn ℝ (1 + 1) v Ω
  rw [contDiffOn_succ_iff_fderiv_of_isOpen hΩ]
  exact ⟨fun x hx ↦ (hv x hx).differentiableAt.differentiableWithinAt, by simp,
    hGcont.congr (fun x hx ↦ (hv x hx).fderiv)⟩

namespace C2Holder

variable {Ω K : Set E} {hΩK : Ω ⊆ K} {α : ℝ}

theorem hasFDerivAt_value_extension (f : C2Holder (F := F) hΩK α) {x : E} (hx : x ∈ Ω) :
    HasFDerivAt (boundedZeroExtension (C2Holder.value f))
      (boundedZeroExtension (C2Holder.firstDerivative f) x) x := by
  rw [boundedZeroExtension_apply _ (hΩK hx)]
  exact C2Holder.hasFDerivAt_value f hx

theorem hasFDerivAt_first_extension (f : C2Holder (F := F) hΩK α) {x : E} (hx : x ∈ Ω) :
    HasFDerivAt (boundedZeroExtension (C2Holder.firstDerivative f))
      (boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F) (C2Holder.secondDerivative f) x) x := by
  rw [boundedZeroExtension_apply _ (hΩK hx)]
  exact C2Holder.hasFDerivAt_firstDerivative f hx

theorem genuine_derivatives (hΩ : IsOpen Ω) (f : C2Holder (F := F) hΩK α)
    {x : E} (hx : x ∈ Ω) :
    fderiv ℝ (boundedZeroExtension (C2Holder.value f)) x = C2Holder.firstDerivative f ⟨x, hΩK hx⟩ ∧
    fderiv ℝ (fderiv ℝ (boundedZeroExtension (C2Holder.value f))) x =
      C2Holder.secondDerivative f ⟨x, hΩK hx⟩ := by
  refine ⟨(C2Holder.hasFDerivAt_value f hx).fderiv, ?_⟩
  have heq : fderiv ℝ (boundedZeroExtension (C2Holder.value f)) =ᶠ[𝓝 x]
      boundedZeroExtension (C2Holder.firstDerivative f) := by
    filter_upwards [hΩ.mem_nhds hx] with y hy
    exact (C2Holder.hasFDerivAt_value_extension f hy).fderiv
  exact heq.fderiv_eq.trans (C2Holder.hasFDerivAt_firstDerivative f hx).fderiv

/-- Membership in the complete graph space implies genuine C² regularity. -/
theorem contDiffOn_value (hΩ : IsOpen Ω) (f : C2Holder (F := F) hΩK α) :
    ContDiffOn ℝ 2 (boundedZeroExtension (C2Holder.value f)) Ω :=
  contDiffOn_two_of_derivative_fields hΩ
    (fun _ hx ↦ C2Holder.hasFDerivAt_value_extension f hx)
    (fun _ hx ↦ C2Holder.hasFDerivAt_first_extension f hx)
    ((continuousOn_boundedZeroExtension (F := E →L[ℝ] E →L[ℝ] F)
      (C2Holder.secondDerivative f)).mono hΩK)

end C2Holder
end OAI.Analysis.Normed.Function.Holder
