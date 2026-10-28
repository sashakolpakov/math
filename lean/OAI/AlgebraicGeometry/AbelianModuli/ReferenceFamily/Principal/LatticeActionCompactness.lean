import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Groups
import OAI.RepresentationTheory.Theta.Geometric.LatticeRestrictionAction
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Cover

/-! # Lattice Action Compactness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.LatticeActionCompactness

noncomputable section

/-! A literal principal lattice subgroup has finite index in the
full lattice stabilizer because it is the kernel of the actual action
on the original lattice modulo N. Compactness descends to that kernel. -/

variable {G V : Type*} [Group G] [AddCommGroup V]
  (ρ : G →* (V ≃ₗ[ℤ] V)) (L : AddSubgroup V) [AddGroup.FG L]
  (Γ : Subgroup G) (hΓ : ∀ g, g ∈ Γ ↔ ∀ v, ρ g v ∈ L ↔ v ∈ L)

include hΓ in
theorem principalAction_finiteRelIndex (N : ℕ) (hN : N ≠ 0) :
    ((Groups.principalLatticeSubgroup L N).comap ρ).IsFiniteRelIndex Γ := by
  let A := ρ.comp Γ.subtype
  have hA (g : Γ) (v : V) : A g v ∈ L ↔ v ∈ L := (hΓ g.val).mp g.property v
  let B := RepresentationTheory.Theta.Geometric.LatticeRestrictionAction.latticeRestrictionAction A L hA
  have hker : (RepresentationTheory.Theta.Geometric.Finite.LatticeCongruence.latticeModNAction N B).ker =
      ((Groups.principalLatticeSubgroup L N).comap ρ).subgroupOf Γ := by
    ext g
    rw [show B = RepresentationTheory.Theta.Geometric.LatticeRestrictionAction.latticeRestrictionAction A L hA from rfl,
      RepresentationTheory.Theta.Geometric.LatticeRestrictionAction.latticeRestrictionAction_congruence]
    change (∀ v ∈ L, ∃ w ∈ L, ρ g.val v - v = N • w) ↔
      ((∀ v, v ∈ L ↔ ρ g.val v ∈ L) ∧
        ∀ v ∈ L, ∃ w ∈ L, ρ g.val v - v = N • w)
    exact ⟨fun h => ⟨fun v => (hA g v).symm, h⟩, fun h => h.2⟩
  rw [Subgroup.isFiniteRelIndex_iff_finiteIndex, ← hker]
  exact RepresentationTheory.Theta.Geometric.Finite.LatticeCongruence.latticeModNAction_finiteIndex N hN B

include hΓ in
theorem principalAction_quotient_compact
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [CompactSpace (G ⧸ Γ)] (N : ℕ) (hN : N ≠ 0) :
    CompactSpace (G ⧸ (Groups.principalLatticeSubgroup L N).comap ρ) :=
  NumberTheory.ArithmeticGroups.Lattices.Compact.Cover.Construction.compact_quotient_of_finite_relIndex _ Γ
    (principalAction_finiteRelIndex ρ L Γ hΓ N hN).relIndex_ne_zero

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Principal.LatticeActionCompactness
