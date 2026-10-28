import OAI.NumberTheory.PadicHodge.Intrinsic
import OAI.NumberTheory.PadicHodge.ThetaParameters
import OAI.NumberTheory.PadicHodge.ThetaArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice

/-! # Frobenius Slope Theta Root -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Model

/-! The original ordinary-model and comparison premises at the same retained root. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
open OAI.RepresentationTheory.Hecke.RadialDilation.Cm
open OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic
open OAI.NumberTheory.PadicHodge.IntrinsicDilation.FrobeniusSlopeIntrinsic

attribute [local instance] IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

theorem comparison_from_retained_root
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (fullSide : Fin s → Bool)
    (hCentralAction : RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished fullSide)
    (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (r a : AlgebraicClosure ℚ) (hr : r ^ 2 = (q : AlgebraicClosure ℚ))
    (hrC : j.complexClosure r = (Real.sqrt (q : ℝ) : ℂ))
    (ha : a ≠ 0) (haC : ‖j.complexClosure a‖ = 1)
    (β : Fin 3 → (AlgebraicClosure ℚ)ˣ)
    (hβ : RepresentationTheory.Hecke.GaloisValuationCm.ProjectivelyEqual (fun i => (β i : AlgebraicClosure ℚ))
      (RepresentationTheory.Hecke.GaloisValuationCm.parameterTriple r a⁻¹))
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (hχβ : ∀ T : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q,
      j.complexClosure (AlgebraicGeometry.HodgeConjecture.CMExtraction.SatakeBaseChange.Iwasawa.torusSatakeOver q β T) = RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ (1 ⊗ₜ[ℚ] T))
    (hCubicRelation : IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.CubicRelationInput.{0, 0, 0, 0})
    (O : IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.OrdinaryData q
      (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).specialFiber.scheme)
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide))
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 1))
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 2))
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished)))
    (hGeometricComparison : GeometricComparison.FrobeniusSlope.GeometricComparisonInput)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).complexFiber (j.complexClosure.comp j.fieldInClosure)).scheme.left
      ((IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).complexFiber (j.complexClosure.comp j.fieldInClosure)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓq : ℓ ≠ q) :
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) r b a ℓ := by
  obtain ⟨b, hb, hcentral, hvalues⟩ := ThetaParameters.FrobeniusSlope.central_values_from_retained_root
    D hg hq hIsogenyQuotient A hTateComparison fullSide hCentralAction j.complexClosure r a hrC ha β hβ χ hχ hχβ
  refine ⟨b, hb, hcentral, hvalues, ?_⟩
  have hp := IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.specialized_polynomial_from_full_CubicRelation (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j)
    (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
    (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 1)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 2)
    (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished) hCubicRelation O
  exact IntrinsicComparison.FrobeniusSlopeIntrinsic.comparison_forced_from_full_GeometricComparison (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j)
    j.fieldInClosure j.complexClosure j.iota (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
    (@hGeometricComparison) j.closure_compatibility.symm ℓ hℓq (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide) hp
    (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
    (IntrinsicModel.FrobeniusSlopeIntrinsic.native_character_occurs D hg hq hIsogenyQuotient A hTateComparison j χ hχ)
    r b a hr hrC haC hcentral hvalues

end NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Model

namespace NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot

/-! Shared native premises and the root-comparison predicate with explicit closure maps. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary
open OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

namespace Conclusion
attribute [local instance] IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
  (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)

abbrev NativeOrdinary (fullSide : Fin s → Bool) :=
  IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.OrdinaryData q
      (AlgebraicGeometry.FormalGeometry.Completion.Endomorphisms.Construction.rationalAlgebraicFrobenius (ZMod q) (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).specialFiber.scheme)
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.C0 s q D.reference.distinguished fullSide))
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 1))
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.MinusculeParameters.nativeMinusculeHecke D (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.actionProjection D A) 2))
      (AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke.specializedHeckeAction (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j)
        (AlgebraicGeometry.AbelianScheme.CentralAction.CentralRepresentatives.Construction.T3 s q D.reference.distinguished))

abbrev NativeProjective :=
  AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).complexFiber (j.complexClosure.comp j.fieldInClosure)).scheme.left
      ((IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).complexFiber (j.complexClosure.comp j.fieldInClosure)).scheme.hom

end Conclusion

namespace CM.ExtremeSlopesAdapter.Geometric
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion

attribute [local instance] IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (jC : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])

def RootComparisonAt
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) : Prop :=
  let r := RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q jC
  ∀ (fullSide : Fin s → Bool), RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished fullSide →
  ∀ (f : K →+* ℚ_[q])
    (hf : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f =
      ι.comp (AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC D.complexEmbedding).toRingHom),
    let j := AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices.qadicChoiceInChosenClosure D.complexEmbedding jC ι f hf
    IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.CubicRelationInput.{0, 0, 0, 0} → Conclusion.NativeOrdinary D hg hq hIsogenyQuotient A hA j fullSide →
    GeometricComparison.FrobeniusSlope.GeometricComparisonInput →
    ∀ (P : Conclusion.NativeProjective D hg hq j) (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ q →
      ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
        (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
        (∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A jC χ hχ (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide i) =
          IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
        IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure jC ι
          (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) P
          (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A jC χ hχ) r b a ℓ

end CM.ExtremeSlopesAdapter.Geometric

end NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot

namespace NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion

/-! Fixed-witness arithmetic and comparison conclusions. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Specialized.CM.Hecke
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary
open OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

attribute [local instance] IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E] [IsGalois ℚ E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
  (hA : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (ιE : E →ₐ[ℚ] AlgebraicClosure ℚ)

/-- The compatible-place premise fixes the ordinary model at the chosen complex and
`q`-adic embeddings. -/
def RootComparison
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) : Prop :=
  CM.ExtremeSlopesAdapter.Geometric.RootComparisonAt E D hg hq hIsogenyQuotient A hA
    (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
    (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) χ hχ a

variable (v : AlgebraicGeometry.HodgeConjecture.CMExtraction.Multiplicity.Odd.Sign E) (rCM : Eˣ) (M : ℕ) (ω ζ : ℂ)

/-- The theta-arithmetic parameter data and root comparison share the same period,
phase, algebraic root, auxiliary scalar, and Satake witnesses. -/
def RetainedParameters
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
    RootComparison E D hg hq hIsogenyQuotient A hA ιE χ hχ a

theorem retainedParameters_of_GaloisValuation
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : RepresentationTheory.Hecke.GeometricParameters.GaloisValuation.ParameterConclusion E q ιE
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) v
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.reference) rCM M ω ζ (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ)) :
    RetainedParameters E D hg hq hIsogenyQuotient A hA ιE v rCM M ω ζ χ hχ := by
  obtain ⟨Ω, Ζ, a, e, β, hd⟩ :=
    (ThetaArithmetic.FrobeniusSlope.parameterConclusion_iff E q ιE _ v _ rCM M ω ζ _).mp h
  obtain ⟨hunit, hbase, hgal⟩ :=
    ThetaArithmetic.FrobeniusSlope.retained_raw_signs E q ιE _ v _ rCM M ω ζ _ Ω Ζ a e β hd
  refine ⟨Ω, Ζ, a, e, β, hd, hunit, hbase, hgal, ?_⟩
  obtain ⟨_, _, ha, _, he, _, _, hβ, hχβ, _⟩ := hd
  intro fullSide hCentralAction f hf j hCubicRelation O hGeometricComparison P ℓ _ hℓq
  exact Model.comparison_from_retained_root D hg hq hIsogenyQuotient A hA fullSide hCentralAction j
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q j.complexClosure) a
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_sq q j.complexClosure)
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt_image q j.complexClosure) ha (hunit 1)
    β (he ▸ hβ) χ hχ hχβ hCubicRelation O (@hGeometricComparison) P ℓ hℓq

theorem retainedParameters_to_GaloisValuation
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (h : RetainedParameters E D hg hq hIsogenyQuotient A hA ιE v rCM M ω ζ χ hχ) :
    RepresentationTheory.Hecke.GeometricParameters.GaloisValuation.ParameterConclusion E q ιE
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) v
      (AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Representatives.Multiplicity.nativeRepresentatives E D.reference) rCM M ω ζ (RepresentationTheory.Hecke.Intrinsic.CentralConstraintIntrinsic.nativeActiveCharacter D χ) := by
  obtain ⟨Ω, Ζ, a, e, β, hd, _⟩ := h
  exact (ThetaArithmetic.FrobeniusSlope.parameterConclusion_iff E q ιE _ v _ rCM M ω ζ _).mpr
    ⟨Ω, Ζ, a, e, β, hd⟩

end NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion

end

end OAI
