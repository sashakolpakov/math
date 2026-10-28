import Mathlib

/-! # Identity Component -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.IdentityComponent.Construction

noncomputable section

/-! Connected components for groups with separately continuous multiplication.
This applies to the Zariski topology, without assuming product continuity. -/

open scoped Classical
open Set _root_.TopologicalSpace _root_.Topology

def separateIdentityComponent (H : Type*) [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] [ContinuousInv H] : Subgroup H where
  carrier := connectedComponent (1 : H)
  one_mem' := mem_connectedComponent
  mul_mem' := by
    intro g h hg hh
    rw [connectedComponent_eq hg]
    have hmul : g ∈ connectedComponent (g * h) := by
      apply Continuous.image_connectedComponent_subset (continuous_const_mul g)
      rw [← connectedComponent_eq hh]
      exact ⟨1, mem_connectedComponent, mul_one g⟩
    simpa [← connectedComponent_eq hmul] using (mem_connectedComponent (x := g * h))
  inv_mem' := inv_mem_connectedComponent_one

theorem finite_of_noetherian_totallyDisconnected
    (X : Type*) [TopologicalSpace X] [NoetherianSpace X] [TotallyDisconnectedSpace X] :
    Finite X := by
  have hc : (⋃₀ irreducibleComponents X).Finite :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).sUnion
      (fun s hs => hs.1.2.isPreconnected.subsingleton.finite)
  rw [sUnion_irreducibleComponents] at hc
  exact Finite.of_finite_univ hc

theorem finite_center_of_trivial_connected_normal_solvable
    {H : Type*} [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] [ContinuousInv H] [NoetherianSpace H]
    (hcenter : IsClosed (Subgroup.center H : Set H))
    (hsemi : ∀ N : Subgroup H, N.Normal → IsClosed (N : Set H) →
      IsConnected (N : Set H) → Group.IsSolvable N → N = ⊥) :
    Finite (Subgroup.center H) := by
  let C := Subgroup.center H
  let : SeparatelyContinuousMul C := {
    continuous_const_mul := fun {c} => IsInducing.subtypeVal.continuous_iff.mpr
      ((continuous_const_mul (c : H)).comp continuous_subtype_val)
    continuous_mul_const := fun {c} => IsInducing.subtypeVal.continuous_iff.mpr
      ((continuous_mul_const (c : H)).comp continuous_subtype_val) }
  let : ContinuousInv C := ⟨IsInducing.subtypeVal.continuous_iff.mpr
    (continuous_inv.comp continuous_subtype_val)⟩
  let : NoetherianSpace C := IsInducing.subtypeVal.noetherianSpace
  let A := separateIdentityComponent C
  let N := A.map C.subtype
  have hNC : N ≤ C := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hNnormal : N.Normal := ⟨fun x hx g => by
    simpa [(Subgroup.mem_center_iff.mp (hNC hx)) g] using hx⟩
  have hNclosed : IsClosed (N : Set H) := by
    exact hcenter.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  have hNconnected : IsConnected (N : Set H) :=
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have hNsolvable : Group.IsSolvable N := Group.isSolvable_of_comm fun x y => by
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hNC y.property) x.val
  have hNbot : N = ⊥ := hsemi N hNnormal hNclosed hNconnected hNsolvable
  have hcomponent : connectedComponent (1 : C) = {1} := by
    apply subset_antisymm
    · intro x hx
      have hxN : (x : H) ∈ N := ⟨x, hx, rfl⟩
      rw [hNbot, Subgroup.mem_bot] at hxN
      exact Subtype.ext hxN
    · exact singleton_subset_iff.mpr mem_connectedComponent
  let : TotallyDisconnectedSpace C :=
    totallyDisconnectedSpace_iff_connectedComponent_one.mpr hcomponent
  exact finite_of_noetherian_totallyDisconnected C

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.IdentityComponent.Construction
