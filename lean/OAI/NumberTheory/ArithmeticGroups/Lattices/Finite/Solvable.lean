import OAI.NumberTheory.ArithmeticGroups.Lattices.IdentityComponent
import OAI.NumberTheory.ArithmeticGroups.Lattices.SeparateClosure

/-! # Solvable -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.Solvable.Construction

noncomputable section

/-! Closed normal solvable subgroups are finite when connected normal
solvable subgroups are trivial in a Noetherian group topology. -/

open scoped Classical
open Set _root_.Topology _root_.TopologicalSpace

theorem finite_closed_normal_solvable
    {H : Type*} [Group H] [TopologicalSpace H]
    [SeparatelyContinuousMul H] [ContinuousInv H] [NoetherianSpace H]
    (hsemi : ∀ N : Subgroup H, N.Normal → IsClosed (N : Set H) →
      IsConnected (N : Set H) → Group.IsSolvable N → N = ⊥)
    (L : Subgroup H) [L.Normal] [Group.IsSolvable L] (hL : IsClosed (L : Set H)) :
    Finite L := by
  let : SeparatelyContinuousMul L := {
    continuous_const_mul := fun {c} => IsInducing.subtypeVal.continuous_iff.mpr
      ((continuous_const_mul (c : H)).comp continuous_subtype_val)
    continuous_mul_const := fun {c} => IsInducing.subtypeVal.continuous_iff.mpr
      ((continuous_mul_const (c : H)).comp continuous_subtype_val) }
  let : ContinuousInv L := ⟨IsInducing.subtypeVal.continuous_iff.mpr
    (continuous_inv.comp continuous_subtype_val)⟩
  let : NoetherianSpace L := IsInducing.subtypeVal.noetherianSpace
  let A := IdentityComponent.Construction.separateIdentityComponent L
  let N := A.map L.subtype
  have hNL : N ≤ L := by rintro _ ⟨y, _, rfl⟩; exact y.property
  have hnormal : N.Normal := by
    constructor
    intro x hx g
    obtain ⟨u, hu, rfl⟩ := hx
    let f : L → L := fun y => ⟨g * y.val * g⁻¹,
      Subgroup.Normal.conj_mem inferInstance y.val y.property g⟩
    have hf : Continuous f := by
      apply Continuous.subtype_mk
      exact ((continuous_mul_const g⁻¹).comp (continuous_const_mul g)).comp continuous_subtype_val
    have hf1 : f 1 = 1 := by apply Subtype.ext; simp [f]
    have hcomp := hf.image_connectedComponent_subset (1 : L)
    rw [hf1] at hcomp
    exact ⟨f u, hcomp ⟨u, hu, rfl⟩, rfl⟩
  have hclosed : IsClosed (N : Set H) :=
    hL.isClosedEmbedding_subtypeVal.isClosedMap _ isClosed_connectedComponent
  have hconnected : IsConnected (N : Set H) :=
    isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have hsolvable : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective hNL)
  have hN : N = ⊥ := hsemi N hnormal hclosed hconnected hsolvable
  have hc : connectedComponent (1 : L) = {1} := by
    apply subset_antisymm
    · intro u hu
      have huN : u.val ∈ N := ⟨u, hu, rfl⟩
      rw [hN, Subgroup.mem_bot] at huN
      exact Subtype.ext huN
    · exact singleton_subset_iff.mpr mem_connectedComponent
  let : TotallyDisconnectedSpace L :=
    totallyDisconnectedSpace_iff_connectedComponent_one.mpr hc
  exact IdentityComponent.Construction.finite_of_noetherian_totallyDisconnected L

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.Solvable.Construction
