import OAI.NumberTheory.ArithmeticGroups.Lattices.ClosedOrbitQuotient

/-! # Stabilizer Saturation -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation.Construction

noncomputable section

/-! A closed integral orbit makes the corresponding stabilizer orbit in
the ambient arithmetic quotient closed. -/

open scoped Classical
open Set MulAction

theorem stabilizer_quotient_saturation
    {H X : Type*} [Group H] [MulAction H X] (Γ : Subgroup H) (x : X) :
    (QuotientGroup.mk : H → H ⧸ Γ) ⁻¹'
      ((QuotientGroup.mk : H → H ⧸ Γ) '' (stabilizer H x : Set H)) =
      {h | h⁻¹ • x ∈ orbit Γ x} := by
  ext h
  constructor
  · rintro ⟨g, hg, he⟩
    have hγ : g⁻¹ * h ∈ Γ := QuotientGroup.eq.mp he
    refine ⟨(⟨g⁻¹ * h, hγ⟩ : Γ)⁻¹, ?_⟩
    change (g⁻¹ * h)⁻¹ • x = h⁻¹ • x
    rw [mul_inv_rev, inv_inv, mul_smul, show g • x = x from hg]
  · rintro ⟨γ, hγ⟩
    change γ.val • x = h⁻¹ • x at hγ
    refine ⟨h * γ.val, ?_, ?_⟩
    · change (h * γ.val) • x = x
      rw [mul_smul]
      rw [hγ, smul_inv_smul]
    · apply QuotientGroup.eq.mpr
      simpa only [mul_inv_rev, inv_mul_cancel_right] using Γ.inv_mem γ.property

theorem stabilizer_image_closed_of_orbit_closed
    {H X : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]
    (Γ : Subgroup H) (x : X) (hx : IsClosed (orbit Γ x)) :
    IsClosed ((QuotientGroup.mk : H → H ⧸ Γ) '' (stabilizer H x : Set H)) := by
  rw [← (QuotientGroup.isQuotientMap_mk Γ).isClosed_preimage, stabilizer_quotient_saturation]
  exact hx.preimage (continuous_inv.smul continuous_const)

theorem stabilizer_image_closed_of_discrete_invariant_set
    {H X : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]
    (Γ : Subgroup H) (x : X) (L : Set X) (hLclosed : IsClosed L)
    (hLdiscrete : IsDiscrete L) (hx : x ∈ L)
    (hstable : ∀ γ ∈ Γ, ∀ y ∈ L, γ • y ∈ L) :
    IsClosed ((QuotientGroup.mk : H → H ⧸ Γ) '' (stabilizer H x : Set H)) := by
  apply stabilizer_image_closed_of_orbit_closed Γ x
  apply isClosed_of_subset_discrete_closed _ hLdiscrete hLclosed
  rintro _ ⟨γ, rfl⟩
  exact hstable γ.val γ.property x hx

theorem subgroup_orbit_eq_quotient_image
    {H : Type*} [Group H] (G Γ : Subgroup H) :
    orbit G (QuotientGroup.mk (1 : H) : H ⧸ Γ) =
      (QuotientGroup.mk : H → H ⧸ Γ) '' (G : Set H) := by
  ext q
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨g.val, g.property, ?_⟩
    change QuotientGroup.mk g.val = QuotientGroup.mk (g.val * 1)
    rw [mul_one]
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, hg⟩, ?_⟩
    change QuotientGroup.mk (g * 1) = QuotientGroup.mk g
    rw [mul_one]

theorem subgroup_quotient_embedding_of_closed_image
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (G Γ : Subgroup H) [SigmaCompactSpace G] [T2Space (H ⧸ Γ)]
    [LocallyCompactSpace (H ⧸ Γ)]
    (hclosed : IsClosed ((QuotientGroup.mk : H → H ⧸ Γ) '' (G : Set H))) :
    Topology.IsClosedEmbedding (ClosedOrbitQuotient.Construction.subgroupCosetMap G Γ) := by
  let : ContinuousSMul G (H ⧸ Γ) := ⟨by
    exact (continuous_subtype_val.comp continuous_fst).smul continuous_snd⟩
  have horbit : IsClosed (orbit G (QuotientGroup.mk (1 : H) : H ⧸ Γ)) := by
    rwa [subgroup_orbit_eq_quotient_image]
  have hs : stabilizer G (QuotientGroup.mk (1 : H) : H ⧸ Γ) = Γ.subgroupOf G := by
    ext g
    change (g.val • (QuotientGroup.mk (1 : H) : H ⧸ Γ)) = QuotientGroup.mk (1 : H) ↔ g.val ∈ Γ
    simp [QuotientGroup.eq]
  have he := ClosedOrbitQuotient.Construction.closed_orbit_quotient_embedding
    (G := G) (QuotientGroup.mk (1 : H) : H ⧸ Γ) horbit
  have hcomp := he.comp (ClosedOrbitQuotient.Construction.quotientHomeomorphOfEq hs.symm).isClosedEmbedding
  convert hcomp using 1
  funext q
  obtain ⟨g, rfl⟩ := Quotient.exists_rep q
  rw [Function.comp_apply, ClosedOrbitQuotient.Construction.quotientHomeomorphOfEq_mk]
  change QuotientGroup.mk g.val = g.val • (QuotientGroup.mk (1 : H) : H ⧸ Γ)
  simp

theorem stabilizer_quotient_embedding_of_discrete_invariant_set
    {H X : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [TopologicalSpace X] [MulAction H X] [ContinuousSMul H X]
    (Γ : Subgroup H) (x : X) [SigmaCompactSpace (stabilizer H x)]
    [T2Space (H ⧸ Γ)] [LocallyCompactSpace (H ⧸ Γ)]
    (L : Set X) (hLclosed : IsClosed L) (hLdiscrete : IsDiscrete L) (hx : x ∈ L)
    (hstable : ∀ γ ∈ Γ, ∀ y ∈ L, γ • y ∈ L) :
    Topology.IsClosedEmbedding (ClosedOrbitQuotient.Construction.subgroupCosetMap (stabilizer H x) Γ) :=
  subgroup_quotient_embedding_of_closed_image (stabilizer H x) Γ
    (stabilizer_image_closed_of_discrete_invariant_set Γ x L hLclosed hLdiscrete hx hstable)

theorem compact_subgroup_quotient_of_compact_container
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (G Γ : Subgroup H) [SigmaCompactSpace G] [T2Space (H ⧸ Γ)]
    [LocallyCompactSpace (H ⧸ Γ)]
    (hclosed : IsClosed ((QuotientGroup.mk : H → H ⧸ Γ) '' (G : Set H)))
    (K : Set (H ⧸ Γ)) (hK : IsCompact K)
    (hbound : ∀ g ∈ G, (QuotientGroup.mk g : H ⧸ Γ) ∈ K) :
    CompactSpace (G ⧸ Γ.subgroupOf G) := by
  have he := subgroup_quotient_embedding_of_closed_image G Γ hclosed
  have hpre : ClosedOrbitQuotient.Construction.subgroupCosetMap G Γ ⁻¹' K = univ := by
    apply eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    exact hbound g.val g.property
  exact ⟨hpre ▸ he.isCompact_preimage hK⟩

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation.Construction
