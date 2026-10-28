import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedPolynomialSectionMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.ProjectiveAugmentation

/-! # Polynomial Twisting Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.PolynomialTwistingSections

noncomputable section

/-! In the uniform Hilbert degree range, the canonical polynomial
section map is surjective. For a saturated flat family it is an actual
linear equivalence with twisting sections, with its original formula. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.ProjectiveAugmentation.GradedHilbert
universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)

include hP

theorem coordinateQuotientTwistingSectionMap_surjective_uniform
    (d : ℕ) (hd : HilbertScheme.Presentations.RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d) :
    Function.Surjective (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d) := by
  have hd' : (HilbertScheme.Presentations.RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
  have haug : Function.Surjective (Cech.DegreeSectionsEquivalence.moduleCechAugmentationSectionsMap (σ := Fin (n + 1)) R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)) := by
    intro z
    obtain ⟨x, hx⟩ := (HilbertScheme.Presentations.Uniform.ProjectiveAugmentation.GradedHilbert.uniform_projective_augmentation_exact I P hP (d : ℤ) hd' z.val).mp z.property
    exact ⟨x, Subtype.ext hx⟩
  exact (ProjectiveTwisting.SectionsCech.projectiveTwistingSectionsCechEquiv I d).symm.surjective.comp
    (haug.comp ((HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)).symm.surjective.comp
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d).surjective))

def coordinateQuotientTwistingSectionEquiv_uniform (hI : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
    (d : ℕ) (hd : HilbertScheme.Presentations.RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d ≃ₗ[R]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
        (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf :=
  LinearEquiv.ofBijective (SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap I d)
    ⟨SaturatedPolynomialSectionMap.coordinateQuotientTwistingSectionMap_injective I hI d,
      coordinateQuotientTwistingSectionMap_surjective_uniform I P hP d hd⟩

theorem homogeneousPolynomialTwistingSectionMap_surjective_uniform
    (d : ℕ) (hd : HilbertScheme.Presentations.RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d) :
    Function.Surjective (SaturatedPolynomialSectionMap.homogeneousPolynomialTwistingSectionMap I d) :=
  (coordinateQuotientTwistingSectionMap_surjective_uniform I P hP d hd).comp
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ_surjective

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Uniform.PolynomialTwistingSections
