import OAI.NumberTheory.PadicHodge.GeometricIntrinsicBridge
import OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot
import OAI.NumberTheory.PadicHodge.Intrinsic
import OAI.NumberTheory.PadicHodge.ThetaParameters
import OAI.NumberTheory.PadicHodge.ThetaArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice

/-! # Extreme Slopes Geometric Root At -/

namespace OAI.NumberTheory.PadicHodge.ExtremeSlopesGeometricRootAt.CM.Adapter.Geometric

noncomputable section

section

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

open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion

variable
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hA : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A) (fullSide : Fin s → Bool)
    (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (r a : AlgebraicClosure ℚ)
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
def NativeComparisonRequest : Prop :=
  IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.CubicRelationInput.{0, 0, 0, 0} → FrobeniusSlopeThetaRoot.Conclusion.NativeOrdinary D hg hq hIsogenyQuotient A hA j fullSide →
  GeometricComparison.FrobeniusSlope.GeometricComparisonInput →
  ∀ (P : FrobeniusSlopeThetaRoot.Conclusion.NativeProjective D hg hq j) (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ q →
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) r b a ℓ

variable (sign : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Bool) (initial : ℚ)

def NativePurityRequest : Prop :=
  IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary.CubicRelationInput.{0, 0, 0, 0} → FrobeniusSlopeThetaRoot.Conclusion.NativeOrdinary D hg hq hIsogenyQuotient A hA j fullSide →
  GeometricComparison.FrobeniusSlope.GeometricComparisonInput →
  ∀ (P : FrobeniusSlopeThetaRoot.Conclusion.NativeProjective D hg hq j) (ℓ : ℕ) [Fact ℓ.Prime], ℓ ≠ q →
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      ExtremeSlopesGeometricForced.CM.Adapter.Geometric.ComparisonHodgeForced (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) r b a ℓ ∧
      ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hA j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
        (fun σ => 1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial / 3)

theorem native_request_add_purity
    (ha : a ≠ 0) (hInitial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hSign : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (j.iota (σ a)) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial)
    (h : NativeComparisonRequest D hg hq hIsogenyQuotient A hA fullSide j r a χ hχ) :
    NativePurityRequest D hg hq hIsogenyQuotient A hA fullSide j r a χ hχ sign initial := by
  intro hCubicRelation O hGeometricComparison P ℓ _ hℓq
  exact GeometricIntrinsicBridge.CM.ExtremeSlopesAdapter.Geometric.native_parameter_comparison_add_purity D hg hq hIsogenyQuotient A hA fullSide j r a χ hχ P ℓ
    sign initial ha hInitial hSign (h hCubicRelation O hGeometricComparison P ℓ hℓq)

theorem native_request_forget_purity
    (h : NativePurityRequest D hg hq hIsogenyQuotient A hA fullSide j r a χ hχ sign initial) :
    NativeComparisonRequest D hg hq hIsogenyQuotient A hA fullSide j r a χ hχ := by
  intro hCubicRelation O hGeometricComparison P ℓ _ hℓq
  exact GeometricIntrinsicBridge.CM.ExtremeSlopesAdapter.Geometric.native_forget_parameter_comparison_purity D hg hq hIsogenyQuotient A hA fullSide j r a χ hχ P ℓ
    sign initial (h hCubicRelation O hGeometricComparison P ℓ hℓq)

end

section

/-! Prove the whole root-family transformation with abstract closure maps.
Only afterwards specialize to the producer's chosen closure constructions. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion

attribute [local instance] IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D) (hA : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (jC : AlgebraicClosure ℚ →+* ℂ)
  (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q])

def RootRequestAt
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) : Prop :=
  let r := RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q jC
  ∀ (fullSide : Fin s → Bool), RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished fullSide →
  ∀ (f : K →+* ℚ_[q])
    (hf : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f =
      ι.comp (AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC D.complexEmbedding).toRingHom),
    let j := AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices.qadicChoiceInChosenClosure D.complexEmbedding jC ι f hf
    NativeComparisonRequest D hg hq hIsogenyQuotient A hA fullSide j r a χ hχ

theorem root_request_eq
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) :
    FrobeniusSlopeThetaRoot.CM.ExtremeSlopesAdapter.Geometric.RootComparisonAt E D hg hq hIsogenyQuotient A hA jC ι χ hχ a =
      RootRequestAt E D hg hq hIsogenyQuotient A hA jC ι χ hχ a := rfl

variable (sign : Gal(AlgebraicClosure ℚ/ℚ) → Bool) (initial : ℚ)

def RootPurityAt
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) : Prop :=
  let r := RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q jC
  ∀ (fullSide : Fin s → Bool), RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.Conclusion D A D.reference.distinguished fullSide →
  ∀ (f : K →+* ℚ_[q])
    (hf : (algebraMap ℚ_[q] (AlgebraicClosure ℚ_[q])).comp f =
      ι.comp (AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices.fieldInChosenClosure jC D.complexEmbedding).toRingHom),
    let j := AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices.qadicChoiceInChosenClosure D.complexEmbedding jC ι f hf
    NativePurityRequest D hg hq hIsogenyQuotient A hA fullSide j r a χ hχ sign initial

theorem root_family_add_purity
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) (ha : a ≠ 0)
    (hInitial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hSign : ∀ σ : Gal(AlgebraicClosure ℚ/ℚ),
      Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (ι (σ a)) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial)
    (h : FrobeniusSlopeThetaRoot.CM.ExtremeSlopesAdapter.Geometric.RootComparisonAt E D hg hq hIsogenyQuotient A hA jC ι χ hχ a) :
    RootPurityAt E D hg hq hIsogenyQuotient A hA jC ι sign initial χ hχ a := by
  have hh := Eq.mp (root_request_eq E D hg hq hIsogenyQuotient A hA jC ι χ hχ a) h
  intro fullSide hCentralAction f hf j
  exact native_request_add_purity D hg hq hIsogenyQuotient A hA fullSide j
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q jC) a χ hχ sign initial ha hInitial hSign
    (hh fullSide hCentralAction f hf)

theorem root_family_forget_purity
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ)
    (h : RootPurityAt E D hg hq hIsogenyQuotient A hA jC ι sign initial χ hχ a) :
    FrobeniusSlopeThetaRoot.CM.ExtremeSlopesAdapter.Geometric.RootComparisonAt E D hg hq hIsogenyQuotient A hA jC ι χ hχ a := by
  apply Eq.mpr (root_request_eq E D hg hq hIsogenyQuotient A hA jC ι χ hχ a)
  intro fullSide hCentralAction f hf j
  exact native_request_forget_purity D hg hq hIsogenyQuotient A hA fullSide j
    (RepresentationTheory.Hecke.IntrinsicArithmetic.GaloisValuationIntrinsic.liftedSqrt q jC) a χ hχ sign initial (h fullSide hCentralAction f hf)

end

/-! Explicit closure-map abstraction for the root comparison predicate. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice.ParameterChoices
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic
open OAI.NumberTheory.PadicHodge.IntrinsicOrdinary.FrobeniusSlopeIntrinsicOrdinary
open OAI.NumberTheory.PadicHodge.FrobeniusSlopeThetaRoot.Conclusion

attribute [local instance] IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable (E : IntermediateField ℚ ℂ) [NumberField E] [NumberField.IsCMField E]
  {K : Type} [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AlgebraicGeometry.AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)
  (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
  (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
  (hA : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
  (ιE : E →ₐ[ℚ] AlgebraicClosure ℚ)

def RootComparisonExactAt
    (_ιE : E →ₐ[ℚ] AlgebraicClosure ℚ)
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ)
    (jC : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) : Prop :=
  FrobeniusSlopeThetaRoot.CM.ExtremeSlopesAdapter.Geometric.RootComparisonAt E D hg hq hIsogenyQuotient A hA jC ι χ hχ a

theorem root_comparison_eq_exact
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ) :
    FrobeniusSlopeThetaRoot.Conclusion.RootComparison E D hg hq hIsogenyQuotient A hA ιE χ hχ a =
      RootComparisonExactAt E D hg hq hIsogenyQuotient A hA ιE χ hχ a
        (RepresentationTheory.Hecke.IntrinsicParameters.GaloisValuationIntrinsic.complexEmbedding E ιE)
        (AlgebraicGeometry.HodgeConjecture.CMExtraction.ClosureSplitting.ParameterChoices.nativeClosureEmbedding D ιE (D.reference.distinguished, false)) := rfl

/-- Compare the two presentations while both closure maps are formal variables. -/
theorem root_exact_eq_at
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (a : AlgebraicClosure ℚ)
    (jC : AlgebraicClosure ℚ →+* ℂ)
    (ι : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ_[q]) :
    RootComparisonExactAt E D hg hq hIsogenyQuotient A hA ιE χ hχ a jC ι =
      FrobeniusSlopeThetaRoot.CM.ExtremeSlopesAdapter.Geometric.RootComparisonAt E D hg hq hIsogenyQuotient A hA jC ι χ hχ a := rfl

end

end OAI.NumberTheory.PadicHodge.ExtremeSlopesGeometricRootAt.CM.Adapter.Geometric
