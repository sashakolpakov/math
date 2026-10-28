import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters

/-! # Ordinary Active Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryActiveCharacter.ParameterChoices

noncomputable section

/-! At the conjugate comparison place, CMPoints's rank-one character is
exactly the original native active integral character. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

theorem ordinary_active_character_of_opposite_place
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hq : D.IsGoodCompletelySplitPrime)
    (J : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (hJ : (HeckeCycles.QadicModelMap.CM.localFieldEmbedding J).comp D.fieldEmbedding =
      LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, true)) :
    J.localCharacter D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) =
      D.localCharacter (D.reference.distinguished, false) := by
  ext a
  apply Subtype.ext
  have hx := RingHom.congr_fun J.integral_compatibility
    (NumberField.RingOfIntegers.mapRingHom (D.fieldEmbedding.comp (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E).toRingHom) a)
  change (J.localCharacter D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E) a : ℚ_[q]) =
    HeckeCycles.QadicModelMap.CM.localFieldEmbedding J (D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (a : E))) at hx
  have hl : HeckeCycles.QadicModelMap.CM.localFieldEmbedding J (D.fieldEmbedding (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (a : E))) =
      LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, true) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (a : E)) :=
    RingHom.congr_fun hJ _
  have hc : LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, true) (ComplexMultiplication.GaloisSigns.CM.CMCoefficientField.conjugation E (a : E)) =
      LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, false) (a : E) :=
    (RingHom.congr_fun (GaloisDiscrete.ParameterChoices.nativeFieldEmbedding_conjugate D hq D.reference.distinguished true) (a : E)).symm
  exact hx.trans (hl.trans (hc.trans (LocalEmbedding.ParameterChoices.nativeFieldEmbedding_onIntegers D _ a)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OrdinaryActiveCharacter.ParameterChoices
