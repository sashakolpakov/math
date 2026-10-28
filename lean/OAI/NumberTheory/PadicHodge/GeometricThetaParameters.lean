import OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot
import OAI.NumberTheory.PadicHodge.GeometricRootValuation
import OAI.NumberTheory.PadicHodge.ExtremeSlopesGeometricRootAt

/-! # Geometric Theta Parameters -/

namespace OAI.NumberTheory.PadicHodge.GeometricThetaParameters.CM.ExtremeSlopesAdapter.Geometric

noncomputable section

/-! Keep FrobeniusSlope's exact retained GaloisValuation root and original compatible-place
premise, and derive terminal ExtremeSlopes purity from its signed valuation. -/

open scoped TensorProduct
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion

attribute [local instance] IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
  (hA : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (ιE : E →ₐ[ℚ] AlgebraicClosure ℚ) (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E)

omit [IsGalois ℚ E] in
/-- The producer's root family is exactly the abstract family at its fixed maps. -/
theorem root_comparison_eq_at
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) :
    FrobeniusSlopeThetaRoot.Conclusion.RootComparison E D hg hq hIsogenyQuotient A hA ιE χ hχ a =
      FrobeniusSlopeThetaRoot.CM.ExtremeSlopesAdapter.Geometric.RootComparisonAt E D hg hq hIsogenyQuotient A hA (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) χ hχ a := by
  exact (ExtremeSlopesGeometricRootAt.CM.Adapter.Geometric.root_comparison_eq_exact E D hg hq hIsogenyQuotient A hA ιE χ hχ a).trans
    (ExtremeSlopesGeometricRootAt.CM.Adapter.Geometric.root_exact_eq_at E D hg hq hIsogenyQuotient A hA ιE χ hχ a
      (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)))

def RootComparisonWithPurity
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) : Prop :=
  ExtremeSlopesGeometricRootAt.CM.Adapter.Geometric.RootPurityAt E D hg hq hIsogenyQuotient A hA (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false))
    (fun σ => v.val (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) (3 / 2) χ hχ a

theorem root_comparison_add_purity
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) (ha : a ≠ 0)
    (hval : ∀ σ : Gal(AlgebraicClosure ℚ/ℚ), RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) (σ a) =
      (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) : ℚ) * (3 / 2))
    (h : FrobeniusSlopeThetaRoot.Conclusion.RootComparison E D hg hq hIsogenyQuotient A hA ιE χ hχ a) :
    RootComparisonWithPurity E D hg hq hIsogenyQuotient A hA ιE v χ hχ a := by
  exact ExtremeSlopesGeometricRootAt.CM.Adapter.Geometric.root_family_add_purity E D hg hq hIsogenyQuotient A hA (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false))
    (fun σ => v.val (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) (3 / 2) χ hχ a ha (Or.inr rfl)
    (fun σ => (GeometricRootValuation.CM.ExtremeSlopesAdapter.Geometric.native_value_eq_canonical q _ (σ a)).symm.trans (hval σ))
    (Eq.mp (root_comparison_eq_at E D hg hq hIsogenyQuotient A hA ιE χ hχ a) h)

theorem forget_root_comparison_purity
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ)
    (h : RootComparisonWithPurity E D hg hq hIsogenyQuotient A hA ιE v χ hχ a) :
    FrobeniusSlopeThetaRoot.Conclusion.RootComparison E D hg hq hIsogenyQuotient A hA ιE χ hχ a := by
  apply Eq.mpr (root_comparison_eq_at E D hg hq hIsogenyQuotient A hA ιE χ hχ a)
  exact ExtremeSlopesGeometricRootAt.CM.Adapter.Geometric.root_family_forget_purity E D hg hq hIsogenyQuotient A hA (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false))
    (fun σ => v.val (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) (3 / 2) χ hχ a h

variable (rCM : Eˣ) (M : ℕ) (ω ζ : ℂ)

def RetainedParametersWithPurity
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥) : Prop :=
  let ι := AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)
  ∃ Ω Ζ a e β,
    ThetaArithmetic.FrobeniusSlope.ParameterData E q ιE ι v (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.reference)
      rCM M ω ζ (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ) Ω Ζ a e β ∧
    (∀ σ : Gal(AlgebraicClosure ℚ/ℚ), ‖RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE (σ a)‖ = 1) ∧
    RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι a = (3 / 2 : ℚ) ∧
    (∀ σ : Gal(AlgebraicClosure ℚ/ℚ), RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.globalValuation q ι (σ a) =
      (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (v.val (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.restriction E ιE σ)) : ℚ) * (3 / 2 : ℚ)) ∧
    RootComparisonWithPurity E D hg hq hIsogenyQuotient A hA ιE v χ hχ a

theorem retained_parameters_add_purity
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : FrobeniusSlopeThetaRoot.Conclusion.RetainedParameters E D hg hq hIsogenyQuotient A hA ιE v rCM M ω ζ χ hχ) :
    RetainedParametersWithPurity E D hg hq hIsogenyQuotient A hA ιE v rCM M ω ζ χ hχ := by
  obtain ⟨Ω, Ζ, a, e, β, hd, hu, hb, hv, hc⟩ := h
  refine ⟨Ω, Ζ, a, e, β, hd, hu, hb, hv, ?_⟩
  exact root_comparison_add_purity E D hg hq hIsogenyQuotient A hA ιE v χ hχ a hd.2.2.1 hv hc

theorem forget_retained_parameters_purity
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : RetainedParametersWithPurity E D hg hq hIsogenyQuotient A hA ιE v rCM M ω ζ χ hχ) :
    FrobeniusSlopeThetaRoot.Conclusion.RetainedParameters E D hg hq hIsogenyQuotient A hA ιE v rCM M ω ζ χ hχ := by
  obtain ⟨Ω, Ζ, a, e, β, hd, hu, hb, hv, hc⟩ := h
  exact ⟨Ω, Ζ, a, e, β, hd, hu, hb, hv,
    forget_root_comparison_purity E D hg hq hIsogenyQuotient A hA ιE v χ hχ a hc⟩

end

end OAI.NumberTheory.PadicHodge.GeometricThetaParameters.CM.ExtremeSlopesAdapter.Geometric
