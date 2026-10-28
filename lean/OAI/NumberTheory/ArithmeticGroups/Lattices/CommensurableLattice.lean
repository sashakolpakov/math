import OAI.NumberTheory.ArithmeticGroups.Lattices.Finite.IndexLattice
import OAI.NumberTheory.ArithmeticGroups.Lattices.LatticeSupergroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.Discrete

/-! # Commensurable Lattice -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.CommensurableLattice.Construction

noncomputable section

/-! The lattice property is invariant under commensurability in a
Hausdorff Polish topological group. -/

theorem lattice_of_commensurable
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [PolishSpace H] [T2Space H]
    (Γ Δ : Subgroup H) (hcomm : Γ.Commensurable Δ) (hΔ : IntegralLattice.IsLattice Δ) : IntegralLattice.IsLattice Γ := by
  let : DiscreteTopology Δ := hΔ.1
  let : DiscreteTopology Γ := hcomm.discreteTopology_iff.mpr inferInstance
  let : ((Γ ⊓ Δ).subgroupOf Δ).FiniteIndex := ⟨by
    change (Γ ⊓ Δ).relIndex Δ ≠ 0
    rw [Subgroup.inf_relIndex_right]
    exact hcomm.1.relIndex_ne_zero⟩
  exact LatticeSupergroup.Construction.lattice_of_discrete_supergroup (Γ ⊓ Δ) Γ inf_le_left
    (Finite.IndexLattice.Construction.lattice_of_finiteIndex_subgroup (Γ ⊓ Δ) Δ inf_le_right hΔ)

theorem lattice_iff_of_commensurable
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [PolishSpace H] [T2Space H]
    (Γ Δ : Subgroup H) (hcomm : Γ.Commensurable Δ) : IntegralLattice.IsLattice Γ ↔ IntegralLattice.IsLattice Δ :=
  ⟨lattice_of_commensurable Δ Γ hcomm.symm, lattice_of_commensurable Γ Δ hcomm⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.CommensurableLattice.Construction
