import OAI.NumberTheory.PadicHodge.ExtremeSlopesGeometricForced
import OAI.NumberTheory.PadicHodge.Intrinsic
import OAI.NumberTheory.PadicHodge.ThetaParameters
import OAI.NumberTheory.PadicHodge.ThetaArithmetic
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CompatibleQadicChoice

/-! # Geometric Intrinsic Bridge -/

namespace OAI.NumberTheory.PadicHodge.GeometricIntrinsicBridge.CM.ExtremeSlopesAdapter.Geometric

noncomputable section

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

variable
    (hg : D.HasIntegralModelGeometry) (hq : D.IsGoodCompletelySplitPrime)
    (hIsogenyQuotient : D.RealizesIsogenyQuotient) (A : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.ActionData D)
    (hTateComparison : AlgebraicGeometry.AbelianScheme.CentralAction.Interface.Construction.Conclusion D hg hq hIsogenyQuotient A)
    (fullSide : Fin s → Bool)
    (j : AlgebraicGeometry.PELModuli.CMPoints.Arithmetic.QadicChoice K D.complexEmbedding q)
    (r a : AlgebraicClosure ℚ)
    (χ : ℂ ⊗[ℚ] AlgebraicGeometry.AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (χ h) ⊤) ≠ ⊥)
    (P : AlgebraicGeometry.Foundations.Scheme.SmoothProjective.ProjectivePresentation
      ((IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).complexFiber (j.complexClosure.comp j.fieldInClosure)).scheme.left
      ((IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j).complexFiber (j.complexClosure.comp j.fieldInClosure)).scheme.hom)
    (ℓ : ℕ) [Fact ℓ.Prime]
    (sign : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → Bool) (initial : ℚ)

theorem native_parameter_comparison_add_purity
    (ha : a ≠ 0) (hInitial : initial = -3 / 2 ∨ initial = 3 / 2)
    (hSign : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      Valuation.CM.ExtremeSlopesAdapter.algebraicValuation q (j.iota (σ a)) = (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial)
    (h :
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) r b a ℓ) :
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      ExtremeSlopesGeometricForced.CM.Adapter.Geometric.ComparisonHodgeForced (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) r b a ℓ ∧
      ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
        (fun σ => 1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial / 3) := by
  exact ExtremeSlopesGeometricForced.CM.Adapter.Geometric.parameter_comparison_add_purity (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
    (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
    (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide)
    r a ℓ sign initial ha hInitial hSign h

theorem native_forget_parameter_comparison_purity
    (h :
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      ExtremeSlopesGeometricForced.CM.Adapter.Geometric.ComparisonHodgeForced (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) r b a ℓ ∧
      ExtremeSlopesGeometricForced.CM.Adapter.Geometric.CharacterPurity (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ)
        (fun σ => 1 / 2 - (AlgebraicGeometry.ComplexMultiplication.SignSwitch.CM.signValue (sign σ) : ℚ) * initial / 3)) :
    ∃ b : AlgebraicClosure ℚ, b ≠ 0 ∧
      (∃ n : ℕ, 0 < n ∧ (b ^ 3 * a) ^ n = 1) ∧
      (∀ i, IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide i) = IntrinsicParameters.FrobeniusSlopeIntrinsic.satakeValues q r b a i) ∧
      IntrinsicComparison.FrobeniusSlopeIntrinsic.ComparisonForced (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
        (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
        (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) r b a ℓ := by
  exact ExtremeSlopesGeometricForced.CM.Adapter.Geometric.forget_parameter_comparison_purity (IntrinsicModel.FrobeniusSlopeIntrinsic.model D hg hq j) j.fieldInClosure j.complexClosure j.iota
    (IntrinsicModel.FrobeniusSlopeIntrinsic.realization D hg hq hIsogenyQuotient A hTateComparison j) P
    (IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j.complexClosure χ hχ) (IntrinsicParameters.FrobeniusSlopeIntrinsic.absorbedHecke D A fullSide)
    r a ℓ sign initial h

end

end OAI.NumberTheory.PadicHodge.GeometricIntrinsicBridge.CM.ExtremeSlopesAdapter.Geometric
