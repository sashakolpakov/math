import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation
import Mathlib.Topology.Algebra.OpenSubgroup

/-! # Open Subgroup Compact Quotient -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.OpenSubgroupCompactQuotient.Construction

noncomputable section

/-! Intersecting a cocompact subgroup with an open subgroup preserves
compactness of the corresponding quotient. -/

open scoped Classical _root_.Topology Pointwise
open Set Filter

theorem open_subgroup_saturation_closed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H Γ : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsClosed ((H : Set G) * (Γ : Set G)) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro g hg
  have hnb : (fun x : G => x * g) '' (H : Set G) ∈ 𝓝 g := by
    simpa only [one_mul] using
      (isOpenMap_mul_right g).image_mem_nhds (hH.mem_nhds H.one_mem)
  apply Filter.mem_of_superset hnb
  rintro x ⟨h, hh, rfl⟩ hx
  obtain ⟨a, ha, b, hb, he⟩ := hx
  apply hg
  refine ⟨h⁻¹ * a, H.mul_mem (H.inv_mem hh) ha, b, hb, ?_⟩
  change (h⁻¹ * a) * b = g
  change a * b = h * g at he
  rw [mul_assoc, he, inv_mul_cancel_left]

theorem open_subgroup_quotient_image_closed
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H Γ : Subgroup G) (hH : IsOpen (H : Set G)) :
    IsClosed ((QuotientGroup.mk : G → G ⧸ Γ) '' (H : Set G)) := by
  rw [← (QuotientGroup.isQuotientMap_mk Γ).isClosed_preimage,
    QuotientGroup.preimage_image_mk_eq_mul]
  exact open_subgroup_saturation_closed H Γ hH

theorem open_subgroup_quotient_compact
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H Γ : Subgroup G) [SigmaCompactSpace H] [T2Space (G ⧸ Γ)]
    [LocallyCompactSpace (G ⧸ Γ)] [CompactSpace (G ⧸ Γ)]
    (hH : IsOpen (H : Set G)) : CompactSpace (H ⧸ Γ.subgroupOf H) := by
  apply StabilizerSaturation.Construction.compact_subgroup_quotient_of_compact_container H Γ
    (open_subgroup_quotient_image_closed H Γ hH) Set.univ isCompact_univ
  exact Set.subset_univ _

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.OpenSubgroupCompactQuotient.Construction
