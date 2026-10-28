import OAI.Geometry.ComplexTorus.RiemannProjectivity.ReducedFamiliesOn

/-! # Glue Reduced -/

namespace OAI.Geometry.ComplexTorus.RiemannProjectivity.GlueReduced.Constructions.GlueReducedFamilies

noncomputable section

/-! # RiemannProjectivity: gluing canonical local polynomial families -/

open Set Filter _root_.Polynomial
open scoped _root_.Topology
open OAI.Geometry.ComplexTorus.RiemannProjectivity.ReducedFamiliesOn.Constructions.ReducedFamilies

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem congr {S : Set (V × ℂ)} {U : Set V} {P Q : V → ℂ[X]}
    (hP : ReducedFamiliesOn.Constructions.ReducedFamilies.On S U P) (heq : EqOn Q P U) : ReducedFamiliesOn.Constructions.ReducedFamilies.On S U Q := by
  refine ⟨fun j => (hP.holomorphic j).congr (fun y hy => congrArg (fun p : ℂ[X] => p.coeff j)
    (heq hy)), ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [heq hy]
    exact hP.monic y hy
  · obtain ⟨k, hk⟩ := hP.constant_degree
    exact ⟨k, fun y hy => by rw [heq hy]; exact hk y hy⟩
  · intro y hy z
    rw [heq hy]
    exact hP.roots y hy z
  · obtain ⟨c, hc, hn, hs⟩ := hP.generic
    exact ⟨c, hc, hn, fun y hy hcy => by rw [heq hy]; exact hs y hy hcy⟩

theorem exists_global {S : Set (V × ℂ)} {B : Set V}
    (hlocal : ∀ x ∈ B, ∃ (U : Set V) (P : V → ℂ[X]),
      IsOpen U ∧ x ∈ U ∧ U ⊆ B ∧ ReducedFamiliesOn.Constructions.ReducedFamilies.On S U P) :
    ∃ Q : V → ℂ[X],
      (∀ j, DifferentiableOn ℂ (fun y => (Q y).coeff j) B) ∧
      (∀ y ∈ B, (Q y).Monic) ∧
      (∀ y ∈ B, ∀ z, (y, z) ∈ S ↔ (Q y).eval z = 0) ∧
      ∀ x ∈ B, ∃ U : Set V, IsOpen U ∧ x ∈ U ∧ U ⊆ B ∧ ReducedFamiliesOn.Constructions.ReducedFamilies.On S U Q := by
  classical
  choose U P hU hxU hUB hP using (fun x : B => hlocal x x.property)
  let Q : V → ℂ[X] := fun y => if hy : y ∈ B then P ⟨y, hy⟩ y else 1
  have hQeq (x : B) : EqOn Q (P x) (U x) := by
    intro y hy
    have hyB := hUB x hy
    simp only [Q, dite_eq_left hyB]
    exact ReducedFamiliesOn.Constructions.ReducedFamilies.eq_at (hU ⟨y, hyB⟩) (hU x) (hP ⟨y, hyB⟩) (hP x)
      (hxU ⟨y, hyB⟩) hy
  have hOn (x : B) : ReducedFamiliesOn.Constructions.ReducedFamilies.On S (U x) Q := GlueReducedFamilies.congr (hP x) (hQeq x)
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro j y hy
    exact (((hOn ⟨y, hy⟩).holomorphic j).differentiableAt
      ((hU ⟨y, hy⟩).mem_nhds (hxU ⟨y, hy⟩))).differentiableWithinAt
  · intro y hy
    exact (hOn ⟨y, hy⟩).monic y (hxU ⟨y, hy⟩)
  · intro y hy
    exact (hOn ⟨y, hy⟩).roots y (hxU ⟨y, hy⟩)
  · intro y hy
    exact ⟨U ⟨y, hy⟩, hU ⟨y, hy⟩, hxU ⟨y, hy⟩, hUB ⟨y, hy⟩, hOn ⟨y, hy⟩⟩

end

end OAI.Geometry.ComplexTorus.RiemannProjectivity.GlueReduced.Constructions.GlueReducedFamilies
