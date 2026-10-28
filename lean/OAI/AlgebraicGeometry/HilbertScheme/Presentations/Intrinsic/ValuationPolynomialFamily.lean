import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ValuationExtension
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Affine.CoefficientPolynomialCriterion

/-! # Valuation Polynomial Family -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ValuationPolynomialFamily.GradedHilbert

noncomputable section

/-! The valuation closure of a saturated generic ideal has the exact
native fiber Hilbert polynomial, on every field-valued test point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped nonZeroDivisors

universe u
variable {S : Scheme.{u}} {R K : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
variable (a : Spec (CommRingCat.of R) ⟶ S)
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading K n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)

def nativeValuationFamilyOfIdeal : Hilbert.Functor.Family (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Over.mk a) := by
  let J := ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I
  let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)) := ValuationClosureFlatness.GradedHilbert.valuationClosure_projective_flat I
  let : LocallyOfFinitePresentation (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading J)) :=
    ValuationClosureFinitePresentation.GradedHilbert.valuationClosure_locallyOfFinitePresentation I hI
  exact HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal n a J

theorem nativeValuationFamilyOfIdeal_coordinates :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n a (nativeValuationFamilyOfIdeal a I hI) =
      ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I := by
  rw [nativeValuationFamilyOfIdeal, HomogeneousFamilyConstruction.GradedHilbert.nativeFamilyOfHomogeneousIdeal_coordinates]
  exact Projective.Saturation.GradedHilbert.projectiveSaturation_eq_of_saturated _ (ContractedIdealSaturation.GradedHilbert.contractedHomogeneousIdeal_saturated I hI)

theorem nativeValuationFamilyOfIdeal_hasFiberHilbertPolynomial
    (P : Polynomial ℚ) (hP : Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P) :
    Has.Core.HasFiberHilbertPolynomial (ProjectivePresentation.GradedHilbert.canonicalProjectivePresentation S n)
      (nativeValuationFamilyOfIdeal a I hI) P := by
  apply Affine.CoefficientPolynomialCriterion.GradedHilbert.hasFiberHilbertPolynomial_of_affine_coefficients a _ P
  intro L _ φ
  rw [nativeValuationFamilyOfIdeal_coordinates]
  let : Algebra R L := φ.toAlgebra
  change Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := L)
    (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I))).toIdeal P
  apply (Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff _ P).mpr
  exact ValuationClosureFunction.GradedHilbert.valuationClosure_hasHilbertPolynomial_baseChange I P hP L

theorem nativeValuationFamilyOfIdeal_generic_coordinates :
    Affine.IntrinsicHomogeneousCoordinates.GradedHilbert.affineNativeHomogeneousIdeal n (Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ a)
      (Hilbert.Functor.pullbackFamily (PolynomialAmbient.GradedHilbert.relativeProjectiveOver S n) (Affine.ProjectiveAmbientNaturality.GradedHilbert.affineTestMap a (algebraMap R K))
        (nativeValuationFamilyOfIdeal a I hI)) = I := by
  rw [Affine.HomogeneousCoordinateBaseChange.GradedHilbert.affineNativeHomogeneousIdeal_baseChange, nativeValuationFamilyOfIdeal_coordinates]
  change Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) (ContractedHomogeneousQuotient.GradedHilbert.contractedHomogeneousIdeal (R := R) I)) = I
  rw [ContractedIdealLocalization.GradedHilbert.contractedHomogeneousIdeal_localization R⁰ I, Projective.Saturation.GradedHilbert.projectiveSaturation_eq_of_saturated I hI]

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Intrinsic.ValuationPolynomialFamily.GradedHilbert
