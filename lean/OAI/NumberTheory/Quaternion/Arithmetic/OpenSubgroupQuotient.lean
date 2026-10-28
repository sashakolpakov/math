import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation

/-! # Open Subgroup Quotient -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.OpenSubgroupQuotient

noncomputable section

/-! Restricting a compact homogeneous quotient to an open subgroup
preserves compactness of its corresponding arithmetic quotient. -/

open scoped Classical
open Set _root_.Topology MulAction OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation.Construction

variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

theorem openSubgroup_cosetMap_isOpen (U Γ : Subgroup H) (hU : IsOpen (U : Set H)) :
    IsOpenMap (ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction.subgroupCosetMap U Γ) := by
  intro S hS
  have hs : IsOpen ((QuotientGroup.mk : U → U ⧸ Γ.subgroupOf U) ⁻¹' S) :=
    hS.preimage QuotientGroup.continuous_mk
  have hv := hU.isOpenMap_subtype_val _ hs
  have hq := QuotientGroup.isOpenMap_coe (N := Γ) _ hv
  have he : (QuotientGroup.mk : H → H ⧸ Γ) ''
      (Subtype.val '' ((QuotientGroup.mk : U → U ⧸ Γ.subgroupOf U) ⁻¹' S)) =
      ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction.subgroupCosetMap U Γ '' S := by
    ext z
    constructor
    · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨QuotientGroup.mk u, hu, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨u, rfl⟩ := Quotient.exists_rep y
      exact ⟨u.val, ⟨u, hy, rfl⟩, rfl⟩
  rw [← he]
  exact hq

theorem openSubgroup_cosetMap_range_closed (U Γ : Subgroup H) (hU : IsOpen (U : Set H)) :
    IsClosed (Set.range (ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction.subgroupCosetMap U Γ)) := by
  let : DiscreteTopology (H ⧸ U) := QuotientGroup.discreteTopology hU
  let x : H ⧸ U := QuotientGroup.mk (1 : H)
  have hstab : stabilizer H x = U := by
    ext g
    change (QuotientGroup.mk (g * 1) : H ⧸ U) = QuotientGroup.mk 1 ↔ g ∈ U
    simp only [mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
  have hc := ArithmeticGroups.Lattices.StabilizerSaturation.Construction.stabilizer_image_closed_of_orbit_closed Γ x (isClosed_discrete (orbit Γ x))
  rw [hstab] at hc
  have he : Set.range (ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction.subgroupCosetMap U Γ) = (QuotientGroup.mk : H → H ⧸ Γ) '' (U : Set H) := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨u, rfl⟩ := Quotient.exists_rep y
      exact ⟨u.val, u.property, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨QuotientGroup.mk (⟨u, hu⟩ : U), rfl⟩
  rw [he]
  exact hc

theorem compact_open_subgroup_quotient (U Γ : Subgroup H) (hU : IsOpen (U : Set H))
    [CompactSpace (H ⧸ Γ)] : CompactSpace (U ⧸ Γ.subgroupOf U) := by
  have he : IsOpenEmbedding (ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction.subgroupCosetMap U Γ) :=
    .of_continuous_injective_isOpenMap (ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction.continuous_subgroupCosetMap U Γ)
      (ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction.subgroupCosetMap_injective U Γ) (openSubgroup_cosetMap_isOpen U Γ hU)
  have hc : IsClosedEmbedding (ArithmeticGroups.Lattices.ClosedOrbitQuotient.Construction.subgroupCosetMap U Γ) :=
    ⟨he.isEmbedding, openSubgroup_cosetMap_range_closed U Γ hU⟩
  exact hc.compactSpace

end

end OAI.NumberTheory.Quaternion.Arithmetic.OpenSubgroupQuotient
