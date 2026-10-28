import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.BoundedLatticeSubgroups
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.ElementaryUniqueness

/-! # Typed Lattice Choices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TypedLatticeChoices.Construction

noncomputable section

/-!
The prescribed abstract rank-three subgroup type selects exactly the
matching bounded Smith lattices. The equivalence is the actual preimage
correspondence under q^(-h)L -> q^(-h)L/L, with no chosen subgroup marking.
-/

variable (q : ℕ) [Fact q.Prime]

abbrev BoundedLatticeQuotient (h : ℕ) (L : Submodule ℤ_[q] (Fin 3 → ℚ_[q])) :=
  BoundedLatticeSubgroups.Construction.qPowerSuperlattice q h L ⧸ L.comap (BoundedLatticeSubgroups.Construction.qPowerSuperlattice q h L).subtype

def boundedSubgroupQuotientEquiv (h : ℕ) (L : Submodule ℤ_[q] (Fin 3 → ℚ_[q]))
    (H : AddSubgroup (BoundedLatticeQuotient q h L)) :
    (BoundedLatticeSubgroups.Construction.boundedLatticeSubgroupOrderIso q h L H).val ⧸
      (L.comap (BoundedLatticeSubgroups.Construction.boundedLatticeSubgroupOrderIso q h L H).val.subtype).toAddSubgroup ≃+ H :=
  BoundedLatticeSubgroups.Construction.subgroupLatticeQuotientEquiv q L (BoundedLatticeSubgroups.Construction.qPowerSuperlattice q h L)
    (BoundedLatticeSubgroups.Construction.le_qPowerSuperlattice q h L) h (BoundedLatticeSubgroups.Construction.qPowerSuperlattice_quotient_killed q h L) H

theorem bounded_subgroup_type_iff_smith (h : ℕ)
    (L : Submodule ℤ_[q] (Fin 3 → ℚ_[q])) [Submodule.IsLattice ℚ_[q] L]
    (H : AddSubgroup (BoundedLatticeQuotient q h L))
    (a : Fin 3 → ℕ) (ha : Antitone a) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput.{0}) :
    Nonempty (H ≃+ (∀ i, ZMod (q ^ a i))) ↔
      ∃ e : Module.Basis (Fin 3) ℚ_[q] (Fin 3 → ℚ_[q]),
        L = Submodule.span ℤ_[q] (Set.range e) ∧
        (BoundedLatticeSubgroups.Construction.boundedLatticeSubgroupOrderIso q h L H).val =
          LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ)) := by
  let M := BoundedLatticeSubgroups.Construction.boundedLatticeSubgroupOrderIso q h L H
  constructor
  · rintro ⟨eA⟩
    obtain ⟨b, ⟨hb, _, e, heL, heM⟩, _⟩ :=
      BoundedLatticeSubgroups.Construction.bounded_subgroup_lattice_type_from_ElementaryDivisors q h L H h_ElementaryDivisors
    let eB : H ≃+ (∀ i, ZMod (q ^ b i)) :=
      (boundedSubgroupQuotientEquiv q h L H).symm.trans
        (Superlattice.Construction.superlatticeQuotientEquiv q L M.val M.property.1 e b heL heM)
    have hab := ElementaryUniqueness.Construction.rankThree_elementary_exponents_unique q Fact.out a b ha hb (eA.symm.trans eB)
    subst b
    exact ⟨e, heL, heM⟩
  · rintro ⟨e, heL, heM⟩
    exact ⟨(boundedSubgroupQuotientEquiv q h L H).symm.trans
      (Superlattice.Construction.superlatticeQuotientEquiv q L M.val M.property.1 e a heL heM)⟩

/-- Fixed elementary subgroup choices and bounded lattices of the same
dominant type are in bijection. No subgroup basis is part of either choice. -/
def typedBoundedLatticeChoicesEquiv (h : ℕ)
    (L : Submodule ℤ_[q] (Fin 3 → ℚ_[q])) [Submodule.IsLattice ℚ_[q] L]
    (a : Fin 3 → ℕ) (ha : Antitone a) (h_ElementaryDivisors : ElementaryDivisors.Construction.ElementaryDivisorsInput.{0}) :
    {H : AddSubgroup (BoundedLatticeQuotient q h L) //
      Nonempty (H ≃+ (∀ i, ZMod (q ^ a i)))} ≃
    {M : Set.Icc L (BoundedLatticeSubgroups.Construction.qPowerSuperlattice q h L) //
      ∃ e : Module.Basis (Fin 3) ℚ_[q] (Fin 3 → ℚ_[q]),
        L = Submodule.span ℤ_[q] (Set.range e) ∧
        M.val = LatticeBounds.Construction.diagonalLattice (q : ℤ_[q]) e (fun i => -(a i : ℤ))} :=
  (BoundedLatticeSubgroups.Construction.boundedLatticeSubgroupOrderIso q h L).toEquiv.subtypeEquiv
    (fun H => bounded_subgroup_type_iff_smith q h L H a ha h_ElementaryDivisors)

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.TypedLatticeChoices.Construction
