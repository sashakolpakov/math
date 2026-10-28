import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterRefinement
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenOccurrence
import OAI.NumberTheory.PadicHodge.IntrinsicModel

/-! # Coefficient Character -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CoefficientCharacter

noncomputable section

/-! The coefficient projector's character is the exact complex full
character consumed by FrobeniusSlope; lifting it back recovers the same coefficients. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors
open OAI.NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic OAI.NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic

attribute [local instance] NumberTheory.PadicHodge.IntrinsicModel.FrobeniusSlopeIntrinsic.heckeCommRing

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  (D : AbelianScheme.TateComparison.Data.SphericalPELAlbaneseData E K s q)

def nativeCoefficientCharacter (j : AlgebraicClosure ℚ →+* ℂ)
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] AlgebraicClosure ℚ) : ℂ ⊗[ℚ] AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℂ] ℂ :=
  ChosenOccurrence.Spectral.fullCharacterOfRational (j.toRatAlgHom.comp χ)

theorem native_coefficient_character_occurs
    (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (j : AlgebraicClosure ℚ →+* ℂ)
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] AlgebraicClosure ℚ)
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.H1))
    (hspace : LinearMap.range P ≤ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.rhoH1 h).baseChange ℂ)
      (fun h => j (χ h)))
    (x : ComplexMultiplication.WeightOne.CM.Complexification D.H1) (hx : P x ≠ 0) :
    (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (nativeCoefficientCharacter j χ h) ⊤) ≠ ⊥ := by
  change HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A) (nativeCoefficientCharacter j χ) ≠ ⊥
  rw [CharacterRefinement.Spectral.jointSpace_scalar_extension]
  simp only [RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction_tmul, one_smul, nativeCoefficientCharacter,
    ChosenOccurrence.Spectral.fullCharacterOfRational_one_tmul, AlgHom.comp_apply]
  exact (Submodule.ne_bot_iff _).mpr ⟨P x, hspace (LinearMap.mem_range_self P x), hx⟩

theorem native_coefficient_character_lift
    (hg : D.HasIntegralModelGeometry) (A : AbelianScheme.CentralAction.Interface.Construction.ActionData D) (j : AlgebraicClosure ℚ →+* ℂ)
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] AlgebraicClosure ℚ)
    (hχ : (⨅ h, (RepresentationTheory.Hecke.Betti.CentralConstraintIntrinsic.nativeFullAction D A h).genEigenspace (nativeCoefficientCharacter j χ h) ⊤) ≠ ⊥) :
    NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter D hg A j (nativeCoefficientCharacter j χ) hχ = χ := by
  apply AlgHom.ext
  intro h
  apply j.injective
  rw [NumberTheory.PadicHodge.IntrinsicParameters.FrobeniusSlopeIntrinsic.algebraicNativeCharacter_image]
  exact ChosenOccurrence.Spectral.fullCharacterOfRational_one_tmul (j.toRatAlgHom.comp χ) h

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CoefficientCharacter
