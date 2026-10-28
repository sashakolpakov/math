import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.Intrinsic.Spectrum
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenOccurrence
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial

/-! # Projector Restriction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectorRestriction.Intrinsic

noncomputable section

/-! Full rational spectral projectors retain commutation and generalized
character-space membership on the actual complex active Hecke algebra. -/

open scoped TensorProduct
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.HeckeCharacters.CM.Projectors OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ChosenOccurrence.Spectral OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.QuotientRadial

variable {E K : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
  [Field K] [NumberField K] {s q : ℕ} [Fact q.Prime]
  {Index Ga MpR MpF MpA : Type} [Fintype Index] [DecidableEq Index]
  [Group Ga] [TopologicalSpace Ga] [Group MpR] [Group MpF] [Group MpA]
  (D : RepresentationTheory.Theta.Geometric.Data.ActiveHeckeThetaData E K s q Index Ga MpR MpF MpA)
  (A : RepresentationTheory.Theta.Geometric.TateComparison.Action D.pel)
  (e : RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q ≃ₐ[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.activeAlgebra q D.pel.reference.distinguished)

def nativeActiveComplexCharacter (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] ℂ) :
    ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q →ₐ[ℂ] ℂ :=
  ChosenOccurrence.Spectral.fullCharacterOfRational (F := ℂ) (H := RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q)
    (χ.comp (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e))

theorem native_projector_active_commute
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1))
    (hP : ∀ h, Commute P ((A.cohomologyAction h).baseChange ℂ))
    (T : ℂ ⊗[ℚ] RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :
    Commute P (Intrinsic.Spectrum.nativeActiveHeckeActionOver D ℂ A e T) := by
  induction T using TensorProduct.inductionOn with
  | add T U hT hU =>
      rw [map_add]
      exact hT.add_right hU
  | tmul c T =>
      apply LinearMap.ext
      intro x
      change P (c • (A.cohomologyAction (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e T)).baseChange ℂ x) =
        c • (A.cohomologyAction (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e T)).baseChange ℂ (P x)
      rw [map_smul]
      exact congrArg (c • ·) (LinearMap.congr_fun (hP _).eq x)

theorem native_projector_active_space
    (hElementaryDivisors : AbelianScheme.TateComparison.Duality.ElementaryDivisorsInput ℤ_[q] ℚ_[q])
    (χ : AbelianScheme.TateComparison.HeckeKernel.Hecke s q →ₐ[ℚ] ℂ)
    (P : Module.End ℂ (ComplexMultiplication.WeightOne.CM.Complexification D.pel.H1))
    (hP : LinearMap.range P ≤ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (fun h => (A.cohomologyAction h).baseChange ℂ) χ) :
    LinearMap.range P ≤ QuotientRadial.jointCharacterSpace q (Intrinsic.Spectrum.nativeActiveHeckeActionOver D ℂ A e)
      (fun T => nativeActiveComplexCharacter D e χ T) := by
  let : CommRing (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q) :=
    { (inferInstance : Ring (RepresentationTheory.Theta.Geometric.SphericalGU.Spherical.SL3Hecke q)) with mul_comm := Radial.Algebra.sl3_hecke_commutative q hElementaryDivisors }
  change LinearMap.range P ≤ HeckeCycles.HeckeCharacters.CM.Projectors.jointSpace (Intrinsic.Spectrum.nativeActiveHeckeActionOver D ℂ A e)
    (nativeActiveComplexCharacter D e χ)
  rw [CharacterRefinement.Spectral.jointSpace_scalar_extension]
  simp only [Intrinsic.Spectrum.nativeActiveHeckeActionOver_tmul, one_smul, nativeActiveComplexCharacter,
    ChosenOccurrence.Spectral.fullCharacterOfRational_one_tmul, AlgHom.comp_apply]
  exact hP.trans (CharacterRefinement.Spectral.jointSpace_restriction_le
    (fun h => (A.cohomologyAction h).baseChange ℂ)
    (RepresentationTheory.Theta.Geometric.Intrinsic.Action.activeHeckeMap q D.pel.reference.distinguished e) χ)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ProjectorRestriction.Intrinsic
