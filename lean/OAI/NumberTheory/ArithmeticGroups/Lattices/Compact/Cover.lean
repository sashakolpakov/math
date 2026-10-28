import OAI.NumberTheory.ArithmeticGroups.Lattices.QuotientMeasure

/-! # Cover -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Cover.Construction

noncomputable section

section

/-! Compact representatives and their behavior under finite-index changes. -/

open scoped Classical Pointwise
open Set

theorem exists_compact_surjects_of_open
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocallyCompactSpace X] [CompactSpace Y]
    (f : X → Y) (hf : IsOpenMap f) (hsurj : Function.Surjective f) :
    ∃ C : Set X, IsCompact C ∧ f '' C = univ := by
  choose K hK hKx using fun x : X => exists_compact_mem_nhds x
  have hcover : (univ : Set Y) ⊆ ⋃ x : X, f '' interior (K x) := by
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    exact mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hKx x), rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => f '' interior (K x)) (fun _ => hf _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ s, K x, s.isCompact_biUnion (fun x _ => hK x), ?_⟩
  apply eq_univ_of_forall
  intro y
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hs (mem_univ y))
  obtain ⟨hxs, z, hz, rfl⟩ := mem_iUnion.mp hx
  exact ⟨z, mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxs, interior_subset hz⟩⟩, rfl⟩

theorem exists_compact_cover_of_compact_quotient
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] (Γ : Subgroup H) [CompactSpace (H ⧸ Γ)] :
    ∃ C : Set H, IsCompact C ∧ ∀ g : H, ∃ c ∈ C, ∃ γ ∈ Γ, g = c * γ := by
  obtain ⟨C, hC, hsurj⟩ := exists_compact_surjects_of_open
    (QuotientGroup.mk : H → H ⧸ Γ) QuotientGroup.isOpenMap_coe QuotientGroup.mk_surjective
  refine ⟨C, hC, fun g => ?_⟩
  obtain ⟨c, hc, he⟩ := hsurj ▸ (mem_univ (QuotientGroup.mk g : H ⧸ Γ))
  refine ⟨c, hc, c⁻¹ * g, QuotientGroup.eq.mp he, ?_⟩
  simp

theorem finite_relIndex_representatives
    {H : Type*} [Group H] (Δ Γ : Subgroup H) (hindex : Δ.relIndex Γ ≠ 0) :
    ∃ R : Set H, R.Finite ∧ ∀ γ ∈ Γ, ∃ r ∈ R, ∃ d ∈ Δ, γ = r * d := by
  let : Δ.IsFiniteRelIndex Γ := ⟨hindex⟩
  let rep : Γ ⧸ Δ.subgroupOf Γ → H := fun q => (q.out : H)
  refine ⟨range rep, finite_range rep, fun γ hγ => ?_⟩
  let g : Γ := ⟨γ, hγ⟩
  let q : Γ ⧸ Δ.subgroupOf Γ := QuotientGroup.mk g
  have hmem : (rep q)⁻¹ * γ ∈ Δ :=
    show q.out⁻¹ * g ∈ Δ.subgroupOf Γ from QuotientGroup.eq.mp q.out_eq'
  exact ⟨rep q, mem_range_self q, (rep q)⁻¹ * γ, hmem, by simp⟩

theorem compact_cover_of_finite_relIndex
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Δ Γ : Subgroup H) (hindex : Δ.relIndex Γ ≠ 0)
    (C : Set H) (hC : IsCompact C)
    (hcover : ∀ g : H, ∃ c ∈ C, ∃ γ ∈ Γ, g = c * γ) :
    ∃ D : Set H, IsCompact D ∧ ∀ g : H, ∃ d ∈ D, ∃ γ ∈ Δ, g = d * γ := by
  obtain ⟨R, hR, hrep⟩ := finite_relIndex_representatives Δ Γ hindex
  refine ⟨C * R, hC.mul hR.isCompact, fun g => ?_⟩
  obtain ⟨c, hc, γ, hγ, rfl⟩ := hcover g
  obtain ⟨r, hr, d, hd, rfl⟩ := hrep γ hγ
  exact ⟨c * r, mul_mem_mul hc hr, d, hd, (mul_assoc c r d).symm⟩

theorem compact_quotient_of_finite_relIndex
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] (Δ Γ : Subgroup H) (hindex : Δ.relIndex Γ ≠ 0)
    [CompactSpace (H ⧸ Γ)] : CompactSpace (H ⧸ Δ) := by
  obtain ⟨C, hC, hcover⟩ := exists_compact_cover_of_compact_quotient Γ
  obtain ⟨D, hD, hDcover⟩ := compact_cover_of_finite_relIndex Δ Γ hindex C hC hcover
  exact QuotientMeasure.Construction.compact_quotient_of_compact_cover Δ D hD hDcover

theorem compact_quotient_iff_of_commensurable
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] (Δ Γ : Subgroup H) (h : Δ.Commensurable Γ) :
    CompactSpace (H ⧸ Δ) ↔ CompactSpace (H ⧸ Γ) := by
  constructor
  · intro hcompact
    exact compact_quotient_of_finite_relIndex Γ Δ h.2.relIndex_ne_zero
  · intro hcompact
    exact compact_quotient_of_finite_relIndex Δ Γ h.1.relIndex_ne_zero

end

/-! Compact subsets of the target of an open surjection admit compact
sets of representatives when the source is locally compact. -/

open Set

theorem exists_compact_cover_of_compact_open_image
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [LocallyCompactSpace X]
    (f : X → Y) (hf : IsOpenMap f) (hsurj : Function.Surjective f)
    (K : Set Y) (hK : IsCompact K) : ∃ C : Set X, IsCompact C ∧ K ⊆ f '' C := by
  choose C hC hCx using fun x : X => exists_compact_mem_nhds x
  have hcover : K ⊆ ⋃ x : X, f '' interior (C x) := by
    intro y _
    obtain ⟨x, rfl⟩ := hsurj y
    exact mem_iUnion.mpr ⟨x, x, mem_interior_iff_mem_nhds.mpr (hCx x), rfl⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : X => f '' interior (C x)) (fun _ => hf _ isOpen_interior) hcover
  refine ⟨⋃ x ∈ s, C x, s.isCompact_biUnion (fun x _ => hC x), ?_⟩
  intro y hy
  obtain ⟨x, hx⟩ := mem_iUnion.mp (hs hy)
  obtain ⟨hxs, z, hz, rfl⟩ := mem_iUnion.mp hx
  exact ⟨z, mem_iUnion.mpr ⟨x, mem_iUnion.mpr ⟨hxs, interior_subset hz⟩⟩, rfl⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.Cover.Construction
