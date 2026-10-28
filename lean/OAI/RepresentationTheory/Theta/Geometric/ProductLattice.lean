import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Product Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric.ProductLattice

noncomputable section

/-! Products of full discrete integer lattices remain full and discrete. -/

variable {V W : Type} [NormedAddCommGroup V] [NormedAddCommGroup W]
  [NormedSpace ℝ V] [NormedSpace ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
  (L : Submodule ℤ V) (M : Submodule ℤ W)

def productLatticeHomeomorph : L.prod M ≃ₜ L × M where
  toEquiv :=
    { toFun := fun v => (⟨v.val.1, v.property.1⟩, ⟨v.val.2, v.property.2⟩)
      invFun := fun v => ⟨(v.1.val, v.2.val), ⟨v.1.property, v.2.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk
    (continuous_subtype_val.snd.subtype_mk _)
  continuous_invFun := ((continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_subtype_val.comp continuous_snd)).subtype_mk _

instance productLattice_discrete [DiscreteTopology L] [DiscreteTopology M] :
    DiscreteTopology (L.prod M) := (productLatticeHomeomorph L M).symm.discreteTopology

instance productLattice_full [DiscreteTopology L] [DiscreteTopology M]
    [IsZLattice ℝ L] [IsZLattice ℝ M] : IsZLattice ℝ (L.prod M) := by
  constructor
  change Submodule.span ℝ ((L : Set V) ×ˢ (M : Set W)) = ⊤
  rw [Submodule.span_prod_eq ℝ L.zero_mem M.zero_mem,
    IsZLattice.span_top (K := ℝ) (L := L), IsZLattice.span_top (K := ℝ) (L := M)]
  ext v
  simp

theorem productLattice_compact [DiscreteTopology L] [DiscreteTopology M]
    [IsZLattice ℝ L] [IsZLattice ℝ M] : CompactSpace ((V × W) ⧸ (L.prod M).toAddSubgroup) := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic (L.prod M)
    (QuotientAddGroup.mk : V × W → (V × W) ⧸ (L.prod M).toAddSubgroup)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

end

end OAI.RepresentationTheory.Theta.Geometric.ProductLattice
