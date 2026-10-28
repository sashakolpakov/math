import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ValuationClosureFinitePresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.GenericUniqueness

/-! # Valuation Extension -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ValuationExtension.GradedHilbert

noncomputable section

/-! The native projective Hilbert-family functor satisfies the full
valuation extension property: restriction to the fraction field is bijective. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped nonZeroDivisors

universe u
variable {S : Scheme.{u}} {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}

theorem nativeFamily_valuation_pullback_surjective (a : Spec (CommRingCat.of R) ⟶ S) :
    Function.Surjective (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
      (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap R K))) := by
  intro F
  let aK := Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a
  let I := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n aK F
  have hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal := Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal_saturated n aK F
  let J := ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I
  have hJ : Hilbert.Polynomial.GradedHilbert.IsSaturated J.toIdeal := ContractedIdealSaturation.GradedHilbert.contractedHomogeneousIdeal_saturated I hI
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)) := ValuationClosureFlatness.GradedHilbert.valuationClosure_projective_flat I
  let : LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)) :=
    ValuationClosureFinitePresentation.GradedHilbert.valuationClosure_locallyOfFinitePresentation I hI
  let G := HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal n a J
  refine ⟨G, ?_⟩
  apply HomogeneousFamilyConstruction.GradedHilbert.affineNativeHomogeneousIdeal_injective n aK
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange]
  change Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K)
    (Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a G)) = I
  rw [HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal_coordinates, Projective.Saturation.GradedHilbert.projectiveSaturation_eq_of_saturated J hJ]
  rw [ContractedIdealLocalization.GradedHilbert.contractedHomogeneousIdeal_localization R⁰ I, Projective.Saturation.GradedHilbert.projectiveSaturation_eq_of_saturated I hI]

theorem nativeFamily_valuation_pullback_bijective (a : Spec (CommRingCat.of R) ⟶ S) :
    Function.Bijective (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n)
      (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap R K))) :=
  ⟨GenericUniqueness.GradedHilbert.nativeFamily_generic_pullback_injective a, nativeFamily_valuation_pullback_surjective a⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ValuationExtension.GradedHilbert
