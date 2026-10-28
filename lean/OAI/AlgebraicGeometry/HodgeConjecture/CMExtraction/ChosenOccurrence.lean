import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Occurrence
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CoefficientOccurrence
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.CentralFinite
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Base
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.CharacterRefinement
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity

/-! # Chosen Occurrence -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenOccurrence

noncomputable section

/-! The full algebraic characters returned by the native comparison
projectors occur over the same chosen algebraic closure. Their occurrence
is proved from the fixed complex embedding, not supplied independently. -/

open scoped TensorProduct

namespace Spectral
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Coefficients.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ChosenCharacters.CM

theorem chosen_character_occurrence
    {U J : Type*} [AddCommGroup U] [Module ℚ U] [FiniteDimensional ℚ U]
    (T : J → Module.End ℚ U) (hcomm : ∀ h k, Commute (T h) (T k))
    (j : AlgebraicClosure ℚ →+* ℂ) (χ : J → AlgebraicClosure ℚ)
    (hχ : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange ℂ) (fun h => j (χ h)) ≠ ⊥) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange (AlgebraicClosure ℚ)) χ ≠ ⊥ := by
  let ψ : J → HeckeCycles.Coefficients.CM.algebraicField := fun h => HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j (χ h)
  have hC : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (T h).baseChange HeckeCycles.Coefficients.CM.algebraicField) ψ ≠ ⊥ :=
    Occurrence.Spectral.complex_joint_occurrence_descends HeckeCycles.Coefficients.CM.algebraicField T hcomm ψ hχ
  have hQ := CoefficientOccurrence.Spectral.coefficientEquiv_occurrence (HeckeCycles.ChosenCharacters.CM.chosenClosureEquiv j).symm T ψ hC
  simpa only [ψ, AlgEquiv.symm_apply_apply] using hQ

def fullCharacterOfRational {F H : Type*} [Field F] [Algebra ℚ F] [Ring H] [Algebra ℚ H]
    (χ : H →ₐ[ℚ] F) : F ⊗[ℚ] H →ₐ[F] F := AlgHom.liftEquiv ℚ F H F χ

theorem fullCharacterOfRational_one_tmul {F H : Type*}
    [Field F] [Algebra ℚ F] [Ring H] [Algebra ℚ H] (χ : H →ₐ[ℚ] F) (h : H) :
    fullCharacterOfRational χ (1 ⊗ₜ[ℚ] h) = χ h := by
  change (1 : F) * χ h = χ h
  exact one_mul _

end Spectral

namespace Intrinsic
open OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Commutativity OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenOccurrence.Spectral
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)

theorem native_chosen_full_occurrence
    (hg : D.pel.HasIntegralModelGeometry) (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q]) (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
    (j : AlgebraicClosure ℚ →+* ℂ) (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] AlgebraicClosure ℚ)
    (hχ : HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.cohomologyAction h).baseChange ℂ) (fun h => j (χ h)) ≠ ⊥) :
    HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.CentralFinite.nativeFullHeckeActionOver D.pel (AlgebraicClosure ℚ) A)
      (Spectral.fullCharacterOfRational (F := AlgebraicClosure ℚ) (H := AbelianScheme.TateComparison.HeckeKernel.Hecke s q) χ) ≠ ⊥ := by
  let : FiniteDimensional ℚ D.pel.H1 := Intrinsic.Base.native_betti_finite D hg
  let : CommRing (AbelianScheme.TateComparison.HeckeKernel.Hecke s q) :=
    { (inferInstance : Ring (AbelianScheme.TateComparison.HeckeKernel.Hecke s q)) with mul_comm := AbelianScheme.TateComparison.Commutativity.spherical_mul_comm s q hElementaryDivisors }
  rw [CharacterRefinement.Spectral.jointSpace_scalar_extension]
  simp only [Intrinsic.CentralFinite.nativeFullHeckeActionOver_tmul, one_smul, Spectral.fullCharacterOfRational_one_tmul]
  exact Spectral.chosen_character_occurrence A.cohomologyAction
    (fun h k => (Commute.all h k).map A.cohomologyAction) j χ hχ

end Intrinsic

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenOccurrence
