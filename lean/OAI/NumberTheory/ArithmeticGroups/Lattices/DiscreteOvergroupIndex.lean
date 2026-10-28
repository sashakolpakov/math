import OAI.NumberTheory.ArithmeticGroups.Lattices.StabilizerSaturation
import Mathlib.GroupTheory.Index

/-! # Discrete Overgroup Index -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.DiscreteOvergroupIndex.Construction

noncomputable section

/-! A discrete overgroup has finite relative index if its image in
the smaller-subgroup quotient lies in a compact set. -/

open scoped Classical

theorem closed_subgroup_quotient_image_of_le
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (Γ Δ : Subgroup H) (hΓΔ : Γ ≤ Δ) (hΔ : IsClosed (Δ : Set H)) :
    IsClosed ((QuotientGroup.mk : H → H ⧸ Γ) '' (Δ : Set H)) := by
  apply (QuotientGroup.isQuotientMap_mk Γ).isClosed_preimage.mp
  have he : (QuotientGroup.mk : H → H ⧸ Γ) ⁻¹'
      ((QuotientGroup.mk : H → H ⧸ Γ) '' (Δ : Set H)) = (Δ : Set H) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      have hm : y⁻¹ * x ∈ Γ := QuotientGroup.eq.mp hxy
      have h := Δ.mul_mem hy (hΓΔ hm)
      simpa only [mul_inv_cancel_left] using! h
    · intro hx
      exact ⟨x, hx, rfl⟩
  rwa [he]

theorem discrete_overgroup_finiteIndex_of_compact_image
    {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (Γ Δ : Subgroup H) (hΓΔ : Γ ≤ Δ)
    [DiscreteTopology Δ] [SigmaCompactSpace Δ]
    [T2Space (H ⧸ Γ)] [LocallyCompactSpace (H ⧸ Γ)]
    (C : Set (H ⧸ Γ)) (hC : IsCompact C)
    (himage : ∀ g ∈ Δ, QuotientGroup.mk g ∈ C) :
    (Γ.subgroupOf Δ).FiniteIndex := by
  have hclosed := closed_subgroup_quotient_image_of_le Γ Δ hΓΔ Δ.isClosed_of_discreteTopology
  have hf := StabilizerSaturation.Construction.subgroup_quotient_embedding_of_closed_image Δ Γ hclosed
  have hpre : ClosedOrbitQuotient.Construction.subgroupCosetMap Δ Γ ⁻¹' C = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    exact himage g.val g.property
  let : CompactSpace (Δ ⧸ Γ.subgroupOf Δ) := ⟨hpre ▸ hf.isCompact_preimage hC⟩
  let : DiscreteTopology (Δ ⧸ Γ.subgroupOf Δ) :=
    QuotientGroup.discreteTopology (isOpen_discrete _)
  exact (Subgroup.finiteIndex_iff_finite_quotient).mpr finite_of_compact_of_discrete

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.DiscreteOvergroupIndex.Construction
