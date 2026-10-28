import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.OppositeParameters

/-! # Opposite Choice Compatibility -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OppositeChoiceCompatibility.ParameterChoices

noncomputable section

/-! A dense ordinary choice with the prescribed opposite closures has the
exact native opposite local field embedding. No new place is chosen. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM

theorem opposite_choice_local_embedding
    (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
    (ιE : E →ₐ[ℚ] ParameterChoices.Qbar)
    {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
    (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q) (hg : D.HasIntegralModelGeometry)
    (hμ : D.reference.μ = E.val.toRingHom) (hq : D.IsGoodCompletelySplitPrime)
    (jC : ParameterChoices.Qbar →+* ℂ) (hι : ∀ x : E, jC (ιE x) = (x : ℂ))
    (J : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (hop : J.iota = Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D)
    (hfield : J.fieldInClosure = (CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC D.complexEmbedding).toRingHom) :
    (HeckeCycles.QadicModelMap.CM.localFieldEmbedding J).comp D.fieldEmbedding =
      LocalEmbedding.ParameterChoices.nativeFieldEmbedding D (D.reference.distinguished, true) := by
  have hE := CompatibleQadicChoice.ParameterChoices.native_fieldInChosenClosure_restrict E D hg hμ jC ιE hι
  ext x
  apply (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).injective
  have h := RingHom.congr_fun J.closure_compatibility (D.fieldEmbedding x)
  rw [hop, hfield] at h
  change Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding E ιE D
    (CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC D.complexEmbedding (D.fieldEmbedding x)) =
      algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q]) (HeckeCycles.QadicModelMap.CM.localFieldEmbedding J (D.fieldEmbedding x)) at h
  have hx : CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC D.complexEmbedding (D.fieldEmbedding x) = ιE x :=
    RingHom.congr_fun hE x
  rw [hx, Intrinsic.OppositeParameters.ParameterChoices.nativeOppositeClosureEmbedding_spec E ιE D hq] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OppositeChoiceCompatibility.ParameterChoices
