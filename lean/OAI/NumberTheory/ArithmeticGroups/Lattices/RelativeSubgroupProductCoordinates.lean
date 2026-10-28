import Mathlib.Topology.Algebra.Group.Subgroup
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.ClosedSubgroupCoordinates

/-! # Relative Subgroup Product Coordinates -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.RelativeSubgroupProductCoordinates.Construction

noncomputable section

/-! Compact/closed product coordinates restricted to a closed
ambient subgroup. -/

open Set

theorem relative_compact_closed_product_isHomeomorph
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (G₀ K P : Subgroup G) (hG₀ : IsClosed (G₀ : Set G))
    (hK : IsCompact (K : Set G)) (hP : IsClosed (P : Set G))
    (hKG : K ≤ G₀) (hPG : P ≤ G₀) (hKP : K ⊓ P = ⊥)
    (hcover : ∀ g ∈ G₀, ∃ k ∈ K, ∃ p ∈ P, k * p = g) :
    IsHomeomorph (fun x : (K.comap G₀.subtype) × (P.comap G₀.subtype) => x.1.val * x.2.val) := by
  have hK' : IsCompact (K.comap G₀.subtype : Set G₀) :=
    hG₀.isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hK
  have hP' : IsClosed (P.comap G₀.subtype : Set G₀) := hP.preimage continuous_subtype_val
  have hKP' : K.comap G₀.subtype ⊓ P.comap G₀.subtype = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    have hx' : x.val ∈ K ⊓ P := hx
    rw [hKP] at hx'
    change x = 1
    exact Subtype.ext hx'
  apply Compact.ClosedSubgroupCoordinates.Construction.compact_closed_subgroup_product_isHomeomorph (K.comap G₀.subtype) (P.comap G₀.subtype) hK' hP' hKP'
  intro g
  obtain ⟨k, hk, p, hp, he⟩ := hcover g.val g.property
  refine ⟨⟨⟨k, hKG hk⟩, hk⟩, ⟨⟨p, hPG hp⟩, hp⟩, ?_⟩
  exact Subtype.ext he

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.RelativeSubgroupProductCoordinates.Construction
