import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion

/-! # Embedding Hodge Membership -/

namespace OAI.AlgebraicGeometry.PELModuli.CMPoints.EmbeddingHodgeMembership

noncomputable section

/-! A rank-three coefficient Hodge structure is determined exactly by
its holomorphic subspaces in every field-embedding coordinate block. -/

open scoped Classical

open OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion

variable (E : Type*) [Field E] [NumberField E] [Algebra ℚ E]
    {U : Type*} [AddCommGroup U] [Module ℚ U] [Module E U] [IsScalarTower ℚ E U]
    (e : U ≃ₗ[E] (Fin 3 → E)) (H : ComplexMultiplication.WeightOne.CM.WeightOneHodgeStructure U)

def embeddingHolomorphicCoordinates (σ : E →ₐ[ℚ] ℂ) : Submodule ℂ (Fin 3 → ℂ) :=
  (H.holomorphic.comap (ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ).subtype).map
    (AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeEmbeddingSpaceEquiv E e σ).toLinearMap

theorem holomorphic_iff_embedding_coordinates
    (hact : ∀ a : E, ComplexMultiplication.WeightOne.CM.IsHodgeMap H H (ComplexMultiplication.WeightOne.CM.scalarEndomorphism E a))
    (u : ComplexMultiplication.WeightOne.CM.Complexification U) :
    u ∈ H.holomorphic ↔ ∀ σ : E →ₐ[ℚ] ℂ,
      AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e u σ ∈ embeddingHolomorphicCoordinates E e H σ := by
  let p := H.holomorphic.projection H.antiholomorphic H.complementary
  constructor
  · intro hu σ
    have hsum : ∑ τ : E →ₐ[ℚ] ℂ, p (AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent E e τ u) = u :=
      (map_sum p _ _).symm.trans
        ((congrArg p (AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponents_sum E e u)).trans
          (Submodule.projection_apply_of_mem_left H.complementary hu))
    have hm (τ : E →ₐ[ℚ] ℂ) :
        p (AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent E e τ u) ∈ ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U τ :=
      AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.embeddingSpace_holomorphicProjection H hact τ _ (AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent_mem E e τ u)
    have hcoord : AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e u σ =
        AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e (p (AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent E e σ u)) σ := by
      conv_lhs => rw [← hsum]
      rw [map_sum, Finset.sum_apply]
      apply Finset.sum_eq_single σ
      · intro τ _ hτσ
        funext i
        exact AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeEmbedding_coordinate_zero E e τ σ hτσ.symm (hm τ) i
      · simp
    exact ⟨⟨p (AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent E e σ u), hm σ⟩,
      Submodule.projection_apply_mem H.complementary _, hcoord.symm⟩
  · intro hu
    have hmem (σ : E →ₐ[ℚ] ℂ) : AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent E e σ u ∈ H.holomorphic := by
      obtain ⟨v, hv, hcoord⟩ := hu σ
      let w : ComplexMultiplication.EmbeddingDecomposition.CM.embeddingSpace E U σ :=
        ⟨AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent E e σ u, AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent_mem E e σ u⟩
      have he : AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeEmbeddingSpaceEquiv E e σ w = AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeEmbeddingSpaceEquiv E e σ v := by
        change AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeComplexCoordinates E e (AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent E e σ u) σ = _
        rw [AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent, LinearEquiv.apply_symm_apply, Pi.single_eq_same]
        exact hcoord.symm
      have hval := congrArg Subtype.val ((AbelianModuli.ReferenceFamily.RankThreeEmbeddingCoordinates.rankThreeEmbeddingSpaceEquiv E e σ).injective he)
      change w.val ∈ H.holomorphic
      rw [hval]
      exact hv
    have hall : (∑ σ : E →ₐ[ℚ] ℂ, AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponent E e σ u) ∈ H.holomorphic :=
      H.holomorphic.sum_mem (fun σ _ => hmem σ)
    exact AbelianModuli.ReferenceFamily.EmbeddingHodgeCriterion.rankThreeEmbeddingComponents_sum E e u ▸ hall

end

end OAI.AlgebraicGeometry.PELModuli.CMPoints.EmbeddingHodgeMembership
