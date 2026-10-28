import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Algebra.Group.Subgroup.Basic

/-! # Invariant Neighborhood -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.InvariantNeighborhood.Construction

/-! A compact subgroup admits a compact neighborhood of the identity
that is invariant under all of its left translations. -/

open scoped Pointwise _root_.Topology
open Set Filter

theorem compact_subgroup_invariant_compact_neighborhood
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    (K : Subgroup G) (hK : IsCompact (K : Set G)) :
    ∃ D : Set G, IsCompact D ∧ D ∈ 𝓝 (1 : G) ∧ ∀ g ∈ K, (g * ·) ⁻¹' D = D := by
  obtain ⟨C, hC, hC₁⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨(K : Set G) * C, hK.mul hC, ?_, ?_⟩
  · exact Filter.mem_of_superset hC₁ (fun x hx => ⟨1, K.one_mem, x, hx, one_mul x⟩)
  · intro g hg
    ext x
    constructor
    · rintro ⟨k, hk, c, hc, h⟩
      refine ⟨g⁻¹ * k, K.mul_mem (K.inv_mem hg) hk, c, hc, ?_⟩
      change k * c = g * x at h
      change (g⁻¹ * k) * c = x
      rw [mul_assoc, h, inv_mul_cancel_left]
    · rintro ⟨k, hk, c, hc, rfl⟩
      exact ⟨g * k, K.mul_mem hg hk, c, hc, mul_assoc g k c⟩

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.InvariantNeighborhood.Construction
