import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Intrinsic.EmbeddingSigns
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.EmbeddedLinearGroup

/-! # Compact Hodge Parts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking

noncomputable section

/-! At the compact embeddings, the prescribed extreme Lie ranks force
the Hodge summand to be zero or the full coordinate space. Any embedded
linear isomorphism preserves the summands of equal extreme rank. -/

variable {E : Type} [Field E] [NumberField E] [Algebra ℚ E]
    {g N : ℕ} {δ : Fin g → ℕ}
    (A : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (ρ : ActionData.IntegralAction (NumberField.RingOfIntegers E) A.abelian)
    (s : ℕ) (hs : 0 < s) (hg : g = 3 * s) (hdegree : Module.finrank ℚ E = 2 * s)
    (τ : E →ₐ[ℚ] ℂ)

theorem nativePositivePart_eq_top_of_rank_zero
    (hr : LieRanks.HasLieRank A.abelian ρ (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 0) :
    Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ = ⊤ :=
  Submodule.eq_top_of_finrank_eq
    ((Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_finrank A ρ s hs hg hdegree τ hr).trans (Module.finrank_fin_fun ℂ).symm)

theorem nativePositivePart_eq_bot_of_rank_three
    (hr : LieRanks.HasLieRank A.abelian ρ (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) 3) :
    Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ = ⊥ :=
  Submodule.finrank_eq_zero.mp (Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart_finrank A ρ s hs hg hdegree τ hr)

theorem nativePositivePart_map_of_extreme_ranks
    (B : HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel g δ N Foundations.Scheme.ProjectiveSpace.complexBase)
    (σ : ActionData.IntegralAction (NumberField.RingOfIntegers E) B.abelian)
    (u : (Fin 3 → E) ≃ₗ[E] (Fin 3 → E)) {r : ℕ} (hr : r = 0 ∨ r = 3)
    (hA : LieRanks.HasLieRank A.abelian ρ (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r)
    (hB : LieRanks.HasLieRank B.abelian σ (τ.toRingHom.comp (algebraMap (NumberField.RingOfIntegers E) E)) r) :
    (Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart A ρ s hs hg hdegree τ).map
      (Matrix.toLin' ((LinearMap.toMatrix' u.toLinearMap).map τ)) =
        Intrinsic.EmbeddingSigns.IntrinsicHermitianMarking.nativeHermitianPositivePart B σ s hs hg hdegree τ := by
  rcases hr with rfl | rfl
  · rw [nativePositivePart_eq_top_of_rank_zero A ρ s hs hg hdegree τ hA,
      nativePositivePart_eq_top_of_rank_zero B σ s hs hg hdegree τ hB, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (EmbeddedLinearGroup.embeddedLinearIso u τ).surjective
  · rw [nativePositivePart_eq_bot_of_rank_three A ρ s hs hg hdegree τ hA,
      nativePositivePart_eq_bot_of_rank_three B σ s hs hg hdegree τ hB, Submodule.map_bot]

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CompactHodgeParts.IntrinsicHermitianMarking
