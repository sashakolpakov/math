import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ParameterChoices
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters

/-! # Lifted Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LiftedRestriction.ParameterChoices

noncomputable section

/-! A lifted coefficient automorphism restricts to exactly the E-automorphism
used by the unchanged CMExtraction extraction statement. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM

theorem lifted_coefficient_restriction
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (L : IntermediateField ℚ ℂ) (hEL : E ≤ L) (hLalg : L ≤ HeckeCycles.Coefficients.CM.algebraicField)
    (j : ParameterChoices.Qbar →+* ℂ) (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    (hι : ∀ x : E, j (ιE x) = (x : ℂ))
    (σ : Gal(L/ℚ)) (τ : Gal(ParameterChoices.Qbar/ℚ))
    (hτ : ∀ a : L,
      j (τ ((HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm (IntermediateField.inclusion hLalg a))) = (σ a : ℂ)) :
    ParameterChoices.restriction E ιE τ = HeckeCycles.Coefficients.CM.coefficientRestriction E L (HeckeCycles.Coefficients.CM.all_embeddings_in_field E L hEL) σ := by
  let hK := HeckeCycles.Coefficients.CM.all_embeddings_in_field E L hEL
  apply (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E).injective
  rw [← HeckeCycles.Coefficients.CM.coefficientRestriction_spec E L hK σ]
  ext x
  have hx : (HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm
      (IntermediateField.inclusion hLalg (IntermediateField.inclusion hEL x)) = ιE x := by
    apply j.injective
    exact (HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv_inverse j _).trans (hι x).symm
  have hc : ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding L E hK (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) x =
      IntermediateField.inclusion hEL x := Subtype.ext rfl
  change ((ParameterChoices.restriction E ιE τ x : E) : ℂ) =
    (σ (ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientEmbedding L E hK (ComplexMultiplication.GaloisCMType.CM.CMCoefficientField.galoisEmbeddingEquiv E 1) x) : ℂ)
  rw [hc]
  calc
    ((ParameterChoices.restriction E ιE τ x : E) : ℂ) = j (ιE (ParameterChoices.restriction E ιE τ x)) := (hι _).symm
    _ = j (τ (ιE x)) := congrArg j (ParameterChoices.restriction_commutes E ιE τ x).symm
    _ = j (τ ((HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm
        (IntermediateField.inclusion hLalg (IntermediateField.inclusion hEL x)))) :=
      congrArg (fun a => j (τ a)) hx.symm
    _ = (σ (IntermediateField.inclusion hEL x) : ℂ) := hτ _

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.LiftedRestriction.ParameterChoices
