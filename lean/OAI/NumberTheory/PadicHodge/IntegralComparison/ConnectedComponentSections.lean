import OAI.RepresentationTheory.Satake.NoetherianConnectedComponents
import Mathlib

/-! # Connected Component Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.ConnectedComponentSections

noncomputable section

/-! Continuous coefficients on a Noetherian space are functions on its actual connected components. -/

open _root_.TopologicalSpace

variable (X : Type*) [TopologicalSpace X] [NoetherianSpace X]

instance components_discrete : DiscreteTopology (ConnectedComponents X) :=
  ConnectedComponents.discreteTopology_iff.mpr
    RepresentationTheory.Satake.NoetherianConnectedComponents.GL.Zariski.noetherian_connectedComponent_isOpen

instance components_finite : Finite (ConnectedComponents X) :=
  RepresentationTheory.Satake.NoetherianConnectedComponents.GL.Zariski.noetherian_connectedComponents_finite

variable (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V]
  [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul R V]
  [TotallyDisconnectedSpace V]

omit [NoetherianSpace X] [AddCommGroup V] [IsTopologicalAddGroup V] in
theorem constant_on_component (f : C(X, V)) {x y : X}
    (h : connectedComponent x = connectedComponent y) : f x = f y := by
  have hx : x ∈ connectedComponent y := h ▸ mem_connectedComponent
  exact (isPreconnected_connectedComponent.image f f.continuous.continuousOn).subsingleton
    ⟨x, hx, rfl⟩ ⟨y, mem_connectedComponent, rfl⟩

def equiv : C(X, V) ≃ₗ[R] (ConnectedComponents X → V) where
  toFun f := Quotient.lift f (fun _ _ h => constant_on_component X V f h)
  invFun f := ⟨fun x => f (ConnectedComponents.mk x),
    continuous_of_discreteTopology.comp ConnectedComponents.continuous_coe⟩
  left_inv f := by ext; rfl
  right_inv f := by
    funext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl
  map_add' f g := by
    funext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl
  map_smul' a f := by
    funext c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    rfl

theorem equiv_apply (f : C(X, V)) (x : X) :
    equiv X R V f (ConnectedComponents.mk x) = f x := rfl

variable {X} {Y : Type*} [TopologicalSpace Y]

def map (f : C(X, Y)) : ConnectedComponents X → ConnectedComponents Y :=
  Quotient.lift (fun x => ConnectedComponents.mk (f x)) (fun x y h => by
    apply ConnectedComponents.coe_eq_coe'.mpr
    exact f.continuous.mapsTo_connectedComponent y (h ▸ mem_connectedComponent))

omit [NoetherianSpace X] in
theorem map_apply (f : C(X, Y)) (x : X) :
    map f (ConnectedComponents.mk x) = ConnectedComponents.mk (f x) := rfl

def perm (e : X ≃ₜ X) : Equiv.Perm (ConnectedComponents X) where
  toFun := map ⟨e, e.continuous⟩
  invFun := map ⟨e.symm, e.symm.continuous⟩
  left_inv c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk (e.symm (e x)) = ConnectedComponents.mk x
    rw [e.symm_apply_apply]
  right_inv c := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change ConnectedComponents.mk (e (e.symm x)) = ConnectedComponents.mk x
    rw [e.apply_symm_apply]

theorem equiv_comp (e : X ≃ₜ X) (f : C(X, V)) (c : ConnectedComponents X) :
    equiv X R V (f.comp ⟨e, e.continuous⟩) c = equiv X R V f (perm e c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.ConnectedComponentSections
