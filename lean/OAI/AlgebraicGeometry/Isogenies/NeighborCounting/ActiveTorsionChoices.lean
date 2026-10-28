import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces
import Mathlib.Algebra.Group.Subgroup.Map

/-! # Active Torsion Choices -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices

noncomputable section

/-! An active elementary subgroup inside higher torsion lies in the
actual q-torsion subgroup. Restriction retains its unmarked subgroup
and yields the required finite-dimensional subspace classification. -/

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTypedSubspaces

variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

def typedSubgroupsBelowEquiv (S : AddSubgroup G) :
    {J : AddSubgroup G // Nonempty (J ≃+ M) ∧ J ≤ S} ≃
      {J : AddSubgroup S // Nonempty (J ≃+ M)} where
  toFun J := ⟨J.val.addSubgroupOf S, J.property.1.map
    (fun e => (AddSubgroup.addSubgroupOfEquivOfLe J.property.2).trans e)⟩
  invFun J := ⟨J.val.map S.subtype,
    ⟨J.property.map (fun e => (J.val.equivMapOfInjective S.subtype Subtype.val_injective).symm.trans e), by
      rintro x ⟨y, _, rfl⟩
      exact y.property⟩⟩
  left_inv J := by
    apply Subtype.ext
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, J.property.2 hx⟩, hx, rfl⟩
  right_inv J := by
    apply Subtype.ext
    ext x
    exact AddSubgroup.mem_map_iff_mem Subtype.val_injective

def killedSubgroup (q : ℕ) (G : Type*) [AddCommGroup G] : AddSubgroup G where
  carrier := {x | q • x = 0}
  zero_mem' := nsmul_zero q
  add_mem' hx hy := by
    change q • _ = 0 at hx hy ⊢
    rw [nsmul_add, hx, hy, add_zero]
  neg_mem' hx := by
    change q • _ = 0 at hx ⊢
    rw [smul_neg, hx, neg_zero]

instance killedSubgroupModule (q : ℕ) (G : Type*) [AddCommGroup G] : Module (ZMod q) (killedSubgroup q G) :=
  AddCommGroup.zmodModule (fun x => Subtype.ext x.property)

theorem typed_subgroup_killed (q : ℕ) (hM : ∀ x : M, q • x = 0)
    (J : AddSubgroup G) (hJ : Nonempty (J ≃+ M)) : J ≤ killedSubgroup q G := by
  obtain ⟨e⟩ := hJ
  intro x hx
  have hz : q • (⟨x, hx⟩ : J) = 0 := by
    apply e.injective
    rw [map_nsmul, hM, map_zero]
  exact congrArg Subtype.val hz

def typedKilledRestrictionEquiv (q : ℕ) (hM : ∀ x : M, q • x = 0) :
    {J : AddSubgroup G // Nonempty (J ≃+ M)} ≃
      {J : AddSubgroup (killedSubgroup q G) // Nonempty (J ≃+ M)} :=
  (Equiv.subtypeEquivRight (fun J =>
    ⟨fun h => ⟨h, typed_subgroup_killed q hM J h⟩, fun h => h.1⟩)).trans
      (typedSubgroupsBelowEquiv (killedSubgroup q G))

theorem typedKilledRestrictionEquiv_membership (q : ℕ) (hM : ∀ x : M, q • x = 0)
    (J : {J : AddSubgroup G // Nonempty (J ≃+ M)}) (x : killedSubgroup q G) :
    x ∈ (typedKilledRestrictionEquiv q hM J).val ↔ x.val ∈ J.val := Iff.rfl

variable (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Finite G]

def activeTorsionSubspaceEquiv (i : Fin 3) :
    {J : AddSubgroup G // Nonempty (J ≃+ AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i))} ≃
      {L : Submodule (ZMod q) (killedSubgroup q G) // Module.finrank (ZMod q) L = HeckeExponents.neighborLevel i} :=
  (typedKilledRestrictionEquiv q (HeckeExponents.activeElementaryModule_killed q i)).trans
    (ActiveTypedSubspaces.activeTypedSubspaceEquiv q (killedSubgroup q G) i)

theorem activeTorsionSubspaceEquiv_membership (i : Fin 3)
    (J : {J : AddSubgroup G // Nonempty (J ≃+ AbelianScheme.IsogenyQuotient.ElementaryModules.Construction.RankThreeElementaryModule.{0} q (HeckeExponents.activeExponents i))})
    (x : killedSubgroup q G) :
    x ∈ (activeTorsionSubspaceEquiv q G i J).val ↔ x.val ∈ J.val := Iff.rfl

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ActiveTorsionChoices
