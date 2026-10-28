import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cech.DegreeSectionsEquivalence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ProjectiveTwisting.SectionsCech
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedCechAugmentation

/-! # Saturated Polynomial Section Map -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedPolynomialSectionMap

noncomputable section

/-! Homogeneous coordinate classes of a saturated projective ideal
embed into actual twisting-bundle sections in every nonnegative degree.
The kernel on homogeneous polynomials is exactly the ideal component. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.SaturatedCechAugmentation.GradedHilbert
universe u
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateQuotientTwistingSectionMap (d : ℕ) : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d →ₗ[R]
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf :=
  (ProjectiveTwisting.SectionsCech.projectiveTwistingSectionsCechEquiv I d).symm.toLinearMap.comp
    ((Cech.DegreeSectionsEquivalence.moduleCechAugmentationSectionsMap (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)).comp
      ((HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)).symm.toLinearMap.comp
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d).toLinearMap))

theorem coordinateQuotientTwistingSectionMap_injective (hI : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (d : ℕ) :
    Function.Injective (coordinateQuotientTwistingSectionMap I d) := by
  have haug : Function.Injective (Cech.DegreeSectionsEquivalence.moduleCechAugmentationSectionsMap (σ := Fin (n + 1)) R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)) := by
    intro x y h
    exact HilbertScheme.Presentations.SaturatedCechAugmentation.GradedHilbert.saturatedCechAugmentation_injective I hI d (congrArg Subtype.val h)
  exact (ProjectiveTwisting.SectionsCech.projectiveTwistingSectionsCechEquiv I d).symm.injective.comp
    (haug.comp ((HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ)).symm.injective.comp (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d).injective))

def homogeneousPolynomialTwistingSectionMap (d : ℕ) : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n d →ₗ[R]
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))).obj
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf :=
  (coordinateQuotientTwistingSectionMap I d).comp (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ

theorem homogeneousPolynomialTwistingSectionMap_kernel (hI : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) (d : ℕ) :
    (homogeneousPolynomialTwistingSectionMap I d).ker = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d := by
  ext p
  change coordinateQuotientTwistingSectionMap I d ((HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).mkQ p) = 0 ↔ _
  rw [← map_zero (coordinateQuotientTwistingSectionMap I d),
    (coordinateQuotientTwistingSectionMap_injective I hI d).eq_iff]
  exact Submodule.Quotient.mk_eq_zero _

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SaturatedPolynomialSectionMap
