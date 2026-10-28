import OAI.RepresentationTheory.Theta.Geometric.Holomorphic.HomeomorphInverse
import OAI.RepresentationTheory.Theta.Geometric.InjectiveHolomorphicOpen

/-! # Dimensional Holomorphic Inverse -/

namespace OAI.RepresentationTheory.Theta.Geometric.Finite.DimensionalHolomorphicInverse

noncomputable section

/-! Injective holomorphic maps in equal finite dimensions have holomorphic
local inverses and bijective complex derivatives at every point. -/

set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped _root_.Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]

theorem finiteDimensional_holomorphic_homeomorph_inverse
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F) (q : OpenPartialHomeomorph E F)
    (hq : DifferentiableOn ℂ q q.source) : DifferentiableOn ℂ q.symm q.target := by
  let e := (Module.finBasis ℂ E).equivFunL
  let b : F ≃L[ℂ] (Fin (Module.finrank ℂ E) → ℂ) :=
    (LinearEquiv.ofFinrankEq F (Fin (Module.finrank ℂ E) → ℂ) (by simpa using hdim.symm)).toContinuousLinearEquiv
  let Q := (e.symm.toHomeomorph.transOpenPartialHomeomorph q).transHomeomorph b.toHomeomorph
  have hQ : DifferentiableOn ℂ Q Q.source :=
    b.differentiable.comp_differentiableOn (hq.comp e.symm.differentiable.differentiableOn (fun _ hz => hz))
  have hQi := Holomorphic.HomeomorphInverse.holomorphic_homeomorph_inverse Q hQ
  have hd : DifferentiableOn ℂ (fun y => e.symm (Q.symm (b y))) q.target :=
    e.symm.differentiable.comp_differentiableOn (hQi.comp b.differentiable.differentiableOn (by
      intro y hy
      change b.symm (b y) ∈ q.target
      rwa [b.symm_apply_apply]))
  have heq : (fun y => e.symm (Q.symm (b y))) = q.symm := by
    funext y
    change e.symm (e (q.symm (b.symm (b y)))) = q.symm y
    rw [e.symm_apply_apply, b.symm_apply_apply]
  rwa [heq] at hd

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] in
theorem holomorphic_homeomorph_derivative_injective (q : OpenPartialHomeomorph E F)
    (hq : DifferentiableOn ℂ q q.source) (hi : DifferentiableOn ℂ q.symm q.target)
    {x : E} (hx : x ∈ q.source) : Function.Injective (fderiv ℂ q x) := by
  have heq : (fun z => q.symm (q z)) =ᶠ[𝓝 x] id := by
    filter_upwards [q.open_source.mem_nhds hx] with z hz
    exact q.left_inv hz
  have hd := heq.fderiv_eq (𝕜 := ℂ)
  change fderiv ℂ ((q.symm : F → E) ∘ (q : E → F)) x = fderiv ℂ id x at hd
  rw [fderiv_comp x (hi.differentiableAt (q.open_target.mem_nhds (q.map_source hx)))
    (hq.differentiableAt (q.open_source.mem_nhds hx)), fderiv_id] at hd
  intro u v huv
  have h := congrArg (fun L : E →L[ℂ] E => L u) hd
  have h' := congrArg (fun L : E →L[ℂ] E => L v) hd
  change fderiv ℂ q.symm (q x) (fderiv ℂ q x u) = u at h
  change fderiv ℂ q.symm (q x) (fderiv ℂ q x v) = v at h'
  exact h.symm.trans ((congrArg (fderiv ℂ q.symm (q x)) huv).trans h')

theorem injectiveHolomorphicPartialHomeomorph_inverse
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U) :
    DifferentiableOn ℂ (InjectiveHolomorphicOpen.injectiveHolomorphicPartialHomeomorph hdim hU hf hinj).symm
      (InjectiveHolomorphicOpen.injectiveHolomorphicPartialHomeomorph hdim hU hf hinj).target :=
  finiteDimensional_holomorphic_homeomorph_inverse hdim _ hf

theorem injective_holomorphic_derivative_bijective
    (hdim : Module.finrank ℂ E = Module.finrank ℂ F)
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) (hinj : InjOn f U)
    {x : E} (hx : x ∈ U) : Function.Bijective (fderiv ℂ f x) := by
  have hi : Function.Injective (fderiv ℂ f x) :=
    holomorphic_homeomorph_derivative_injective (InjectiveHolomorphicOpen.injectiveHolomorphicPartialHomeomorph hdim hU hf hinj)
      hf (injectiveHolomorphicPartialHomeomorph_inverse hdim hU hf hinj) hx
  exact ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi⟩

end

end OAI.RepresentationTheory.Theta.Geometric.Finite.DimensionalHolomorphicInverse
