import OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingInverseContinuity
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-! # Contracting Local Homeomorphism -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingLocalHomeomorphism.Construction

noncomputable section

/-! An equivariant local homeomorphism extends globally when compatible
invertible flows contract both its domain and its codomain. -/

open Filter
open scoped _root_.Topology

theorem bijective_of_contracting_local_homeomorphism
    {E F ι : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (f : E → F) (p : OpenPartialHomeomorph E F) (hp : (p : E → F) = f)
    (x₀ : E) (hx₀ : x₀ ∈ p.source)
    (a : ι → E ≃ₜ E) (b : ι → F ≃ₜ F)
    (heq : ∀ t x, f (a t x) = b t (f x)) (l : Filter ι) [NeBot l]
    (ha : ∀ x, Tendsto (fun t => a t x) l (𝓝 x₀))
    (hb : ∀ y, Tendsto (fun t => b t y) l (𝓝 (f x₀))) : Function.Bijective f := by
  constructor
  · intro x y hxy
    obtain ⟨t, htx, hty⟩ := ((ha x).eventually (p.open_source.mem_nhds hx₀) |>.and
      ((ha y).eventually (p.open_source.mem_nhds hx₀))).exists
    apply (a t).injective
    apply p.injOn htx hty
    rw [hp, heq, heq, hxy]
  · intro y
    have hy₀ : f x₀ ∈ p.target := hp ▸ p.map_source hx₀
    obtain ⟨t, ht⟩ := ((hb y).eventually (p.open_target.mem_nhds hy₀)).exists
    refine ⟨(a t).symm (p.symm (b t y)), ?_⟩
    apply (b t).injective
    rw [← heq, (a t).apply_symm_apply, ← hp]
    exact p.right_inv ht

theorem exists_homeomorph_of_contracting_local_homeomorphism
    {E F ι : Type*} [TopologicalSpace E] [TopologicalSpace F]
    (f : E → F) (hf : Continuous f)
    (p : OpenPartialHomeomorph E F) (hp : (p : E → F) = f)
    (x₀ : E) (hx₀ : x₀ ∈ p.source)
    (a : ι → E ≃ₜ E) (b : ι → F ≃ₜ F)
    (heq : ∀ t x, f (a t x) = b t (f x)) (l : Filter ι) [NeBot l]
    (ha : ∀ x, Tendsto (fun t => a t x) l (𝓝 x₀))
    (hb : ∀ y, Tendsto (fun t => b t y) l (𝓝 (f x₀))) :
    ∃ e : E ≃ₜ F, (e : E → F) = f := by
  let e := Equiv.ofBijective f (bijective_of_contracting_local_homeomorphism f p hp x₀ hx₀ a b heq l ha hb)
  have he : (e : E → F) = f := rfl
  have hlocal : ∀ᶠ y in 𝓝 (f x₀), ContinuousAt e.symm y := by
    have hy₀ : f x₀ ∈ p.target := hp ▸ p.map_source hx₀
    filter_upwards [p.open_target.mem_nhds hy₀] with y hy
    have hi : ∀ᶠ z in 𝓝 y, e.symm z = p.symm z := by
      filter_upwards [p.open_target.mem_nhds hy] with z hz
      apply e.injective
      rw [e.apply_symm_apply, he, ← hp, p.right_inv hz]
    exact (p.continuousAt_symm hy).congr_of_eventuallyEq hi
  have hinv : Continuous e.symm := ContractingInverseContinuity.Construction.continuous_inverse_of_contracting_equivariance
    e (fun t => a t) (fun t => (a t).symm) (fun t => b t)
    (fun t => (a t).symm.continuous) (fun t => (b t).continuous)
    (fun t x => (a t).symm_apply_apply x) heq l (f x₀) hb hlocal
  exact ⟨⟨e, hf, hinv⟩, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.ContractingLocalHomeomorphism.Construction
