import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechTermValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechCofaces

/-! # Cech Linear Factors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechLinearFactors

noncomputable section

/-! The nonnegative-twist factor maps as linear maps into the full localization modules. -/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def positiveTwistCechFactorMap (d q : ℕ)
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q) :
    Ordered.CoefficientCechTerms.coefficientCechFactor (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q a.val →ₗ[R]
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a) :=
  (HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a) (d : ℤ)).subtype.comp (CechTermEquivalence.positiveTwistCechFactorEquiv I d q a).toLinearMap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechLinearFactors
