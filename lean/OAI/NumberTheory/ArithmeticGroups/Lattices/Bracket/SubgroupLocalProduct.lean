import OAI.NumberTheory.ArithmeticGroups.Lattices.OrthogonalBracketUnitCompactness
import OAI.NumberTheory.ArithmeticGroups.Lattices.Compact.SubgroupProduct

/-! # Subgroup Local Product -/

namespace OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.SubgroupLocalProduct.Construction

noncomputable section

/-! A local factorization in operator coordinates gives a neighborhood
in a product of subgroups of the bracket automorphism group. -/

open scoped _root_.Topology Pointwise
open Filter Set

theorem bracket_subgroup_product_mem_nhds
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (K P : Subgroup (L →L[ℝ] L)ˣ)
    (hK : K ≤ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) (hP : P ≤ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)
    (hlocal : ∀ᶠ T in 𝓝 (1 : L →L[ℝ] L),
      (∀ x y, T (B x y) = B (T x) (T y)) →
        ∃ k ∈ K, ∃ p ∈ P, (k : L →L[ℝ] L) * (p : L →L[ℝ] L) = T) :
    (K.comap (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).subtype : Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) *
      (P.comap (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).subtype : Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) ∈
      𝓝 (1 : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) := by
  have hc : Continuous (fun g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B => (g.val : L →L[ℝ] L)) :=
    Units.continuous_val.comp continuous_subtype_val
  have ht : Tendsto (fun g : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B => (g.val : L →L[ℝ] L))
      (𝓝 (1 : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) (𝓝 (1 : L →L[ℝ] L)) := hc.continuousAt
  filter_upwards [ht.eventually hlocal] with g hg
  obtain ⟨k, hk, p, hp, he⟩ := hg g.property
  refine ⟨⟨k, hK hk⟩, hk, ⟨p, hP hp⟩, hp, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact he

theorem bracket_identity_component_subset_product
    {L : Type*} [NormedAddCommGroup L] [NormedSpace ℝ L]
    (B : L →L[ℝ] L →L[ℝ] L) (K P : Subgroup (L →L[ℝ] L)ˣ)
    (hK : K ≤ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) (hP : P ≤ UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)
    (hKcomp : IsCompact (K : Set (L →L[ℝ] L)ˣ)) (hPclosed : IsClosed (P : Set (L →L[ℝ] L)ˣ))
    (hlocal : ∀ᶠ T in 𝓝 (1 : L →L[ℝ] L),
      (∀ x y, T (B x y) = B (T x) (T y)) →
        ∃ k ∈ K, ∃ p ∈ P, (k : L →L[ℝ] L) * (p : L →L[ℝ] L) = T) :
    connectedComponent (1 : UnipotentBracketGroup.Construction.continuousBracketUnitGroup B) ⊆
      (K.comap (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).subtype : Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) *
        (P.comap (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).subtype : Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) := by
  have hc : IsCompact (K.comap (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B).subtype : Set (UnipotentBracketGroup.Construction.continuousBracketUnitGroup B)) :=
    (UnipotentBracketGroup.Construction.continuousBracketUnitGroup_isClosed B).isClosedEmbedding_subtypeVal.isProperMap.isCompact_preimage hKcomp
  exact Compact.SubgroupProduct.Construction.connectedComponent_one_subset_compact_subgroup_product _ _ hc
    (hPclosed.preimage continuous_subtype_val) (bracket_subgroup_product_mem_nhds B K P hK hP hlocal)

end

end OAI.NumberTheory.ArithmeticGroups.Lattices.Bracket.SubgroupLocalProduct.Construction
