import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.PadicSubgroups
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Superlattice

/-! # Intermediate Lattices -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntermediateLattices.Construction

noncomputable section

/-!
Subgroups of a bounded lattice quotient correspond to the actual
intermediate lattices. Their q-adic stability and lattice finiteness
are proved, rather than imposed on the subgroup choices.
-/

section Intervals

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def internalIntermediateOrderIso
    (L T : Submodule R V) (hLT : L ≤ T) :
    Set.Ici (L.comap T.subtype) ≃o Set.Icc L T where
  toFun M := ⟨M.val.map T.subtype, by
    constructor
    · have hm := Submodule.map_mono (f := T.subtype)
        (show L.comap T.subtype ≤ M.val from M.property)
      rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr hLT] at hm
      exact hm
    · exact Submodule.map_subtype_le T M.val⟩
  invFun M := ⟨M.val.comap T.subtype, Submodule.comap_mono M.property.1⟩
  left_inv M := Subtype.ext (Submodule.comap_map_eq_of_injective T.injective_subtype M.val)
  right_inv M := Subtype.ext (by
    change (M.val.comap T.subtype).map T.subtype = M.val
    rw [Submodule.map_comap_eq, Submodule.range_subtype, inf_eq_right.mpr M.property.2])
  map_rel_iff' := by
    intro M N
    change M.val.map T.subtype ≤ N.val.map T.subtype ↔ M.val ≤ N.val
    rw [Submodule.map_le_iff_le_comap,
      Submodule.comap_map_eq_of_injective T.injective_subtype]

end Intervals

variable (q : ℕ) [Fact q.Prime] {d : ℕ}

def latticeQuotientSubgroupOrderIso
    (L T : Submodule ℤ_[q] (Fin d → ℚ_[q])) (hLT : L ≤ T) (h : ℕ)
    (hkilled : ∀ x : T ⧸ L.comap T.subtype, (q : ℤ_[q]) ^ h • x = 0) :
    AddSubgroup (T ⧸ L.comap T.subtype) ≃o Set.Icc L T :=
  ((PadicSubgroups.Construction.padicSubgroupOrderIso q h hkilled).trans
    (Submodule.comapMkQRelIso (L.comap T.subtype))).trans
    (internalIntermediateOrderIso L T hLT)

theorem intermediate_isLattice
    (L T : Submodule ℤ_[q] (Fin d → ℚ_[q]))
    [Submodule.IsLattice ℚ_[q] L] [Submodule.IsLattice ℚ_[q] T]
    (M : Set.Icc L T) : Submodule.IsLattice ℚ_[q] M.val :=
  Submodule.IsLattice.of_le_of_isLattice_of_fg ℚ_[q] M.property.1
    ((Submodule.IsLattice.fg (M := T)).of_le M.property.2)

theorem latticeQuotientSubgroup_isLattice
    (L T : Submodule ℤ_[q] (Fin d → ℚ_[q])) (hLT : L ≤ T)
    [Submodule.IsLattice ℚ_[q] L] [Submodule.IsLattice ℚ_[q] T] (h : ℕ)
    (hkilled : ∀ x : T ⧸ L.comap T.subtype, (q : ℤ_[q]) ^ h • x = 0)
    (H : AddSubgroup (T ⧸ L.comap T.subtype)) :
    Submodule.IsLattice ℚ_[q] (latticeQuotientSubgroupOrderIso q L T hLT h hkilled H).val :=
  intermediate_isLattice q L T _

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.IntermediateLattices.Construction
