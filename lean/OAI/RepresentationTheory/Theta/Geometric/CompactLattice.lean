import Mathlib

/-! # Compact Lattice -/

namespace OAI.RepresentationTheory.Theta.Geometric.CompactLattice

noncomputable section

/-! Compactness of the period quotient forces the real span of its
integer lattice to be the whole tangent space. -/

theorem span_top_of_compact_quotient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [CompactSpace (V ⧸ L.toAddSubgroup)] :
    Submodule.span ℝ (L : Set V) = ⊤ := by
  by_contra h
  obtain ⟨f, hf, hker⟩ := (Submodule.span ℝ (L : Set V)).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr h)
  have hL : L.toAddSubgroup ≤ f.toAddMonoidHom.ker := by
    intro x hx
    exact hker (Submodule.subset_span hx)
  let F : V ⧸ L.toAddSubgroup →+ ℝ := QuotientAddGroup.lift L.toAddSubgroup f.toAddMonoidHom hL
  have hcont : Continuous F := continuous_quot_lift _ f.continuous_of_finiteDimensional
  obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hf
  change f x ≠ 0 at hx
  have hsurj : Function.Surjective F := by
    intro y
    refine ⟨QuotientAddGroup.mk ((y / f x) • x), ?_⟩
    change f ((y / f x) • x) = y
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ y hx]
  have hc : IsCompact (Set.univ : Set ℝ) := by
    rw [← Set.range_eq_univ.mpr hsurj]
    exact isCompact_range hcont
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℝ)) (isCompact_univ_iff.mp hc)

theorem isZLattice_of_compact_quotient
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] [CompactSpace (V ⧸ L.toAddSubgroup)] :
    IsZLattice ℝ L := ⟨span_top_of_compact_quotient L⟩

end

end OAI.RepresentationTheory.Theta.Geometric.CompactLattice
