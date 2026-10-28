import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.OppositePurity

/-! # Comparison Conclusion -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.ComparisonConclusion.CMExtractionIntrinsic

noncomputable section

/-! Apply the full FrobeniusSlope comparison and ExtremeSlopes purity to the retained
parameters after the integral ordinary-point polynomial has been transported
to the actual rational Hecke realization. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion

attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (ιE : E →ₐ[ℚ] CMExtraction.ParameterChoices.Qbar) (v : CMExtraction.Multiplicity.Odd.Sign E) (rCM : Eˣ) (M : ℕ) (ω ζ : ℂ)

def FullComparisonConclusion
    (χ : ℂ ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (side : Fin s → Bool) (j : PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (P : NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion.NativeProjective D hg hq j) (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
    ∃ Ω Ζ a e β,
      NumberTheory.PadicHodge.ThetaArithmetic.FrobeniusSlope.ParameterData E q ιE
        (CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) v
        (CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.reference) rCM M ω ζ (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ) Ω Ζ a e β ∧
      (∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), ‖j.complexClosure (σ a)‖ = 1) ∧
      (∀ σ : Gal(CMExtraction.ParameterChoices.Qbar/ℚ), NumberTheory.PadicHodge.Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (j.iota (σ a)) =
        (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2)) ∧
      ∃ b : CMExtraction.ParameterChoices.Qbar, b ≠ 0 ∧ (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
        (∀ i, NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A side i) =
          NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j.complexClosure) b a i) ∧
        NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric.ComparisonHodgeForced (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
          (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) P
          (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
          (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j.complexClosure) b a ℓ ∧
        NumberTheory.PadicHodge.ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure
          (NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) P
          (NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
          (fun σ => 1 / 2 - (ComplexMultiplication.SignSwitch.CM.signValue (v.val (CMExtraction.ParameterChoices.restriction E ιE σ)) : ℚ) * (-3 / 2) / 3)

end

end OAI.AlgebraicGeometry.HodgeConjecture.ComparisonConclusion.CMExtractionIntrinsic
