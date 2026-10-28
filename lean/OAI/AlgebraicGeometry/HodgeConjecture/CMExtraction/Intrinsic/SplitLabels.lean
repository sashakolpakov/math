import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.GaloisDiscrete

/-! # Split Labels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SplitLabels.ParameterChoices

noncomputable section

/-! All native q-adic slots, with their original labels, form the
entire embedding set of the original Galois CM field. -/

open scoped Classical
open _root_.NumberField

variable {E K : Type} [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem nativeFieldAlgEmbedding_bijective (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) :
    Function.Bijective (GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D) := by
  refine ⟨GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding_injective D hq, ?_⟩
  intro f
  let i₀ := (D.reference.distinguished, false)
  obtain ⟨i, hi⟩ := (GaloisDiscrete.ParameterChoices.nativeLocalLabel_bijective D hg hq i₀).surjective
    (GaloisDiscrete.ParameterChoices.embeddingAutEquiv (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i₀) f)
  exact ⟨i, (GaloisDiscrete.ParameterChoices.embeddingAutEquiv (LocalEmbedding.ParameterChoices.nativeFieldEmbedding D i₀)).injective hi⟩

def nativeFieldAlgEmbeddingEquiv (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime) :
    (Fin s × Bool) ≃ (E →ₐ[ℚ] Padic q) :=
  Equiv.ofBijective (GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D) (nativeFieldAlgEmbedding_bijective D hg hq)

theorem nativeFieldAlgEmbeddingEquiv_apply (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (v : Fin s × Bool) : nativeFieldAlgEmbeddingEquiv D hg hq v = GaloisDiscrete.ParameterChoices.nativeFieldAlgEmbedding D v := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.SplitLabels.ParameterChoices
