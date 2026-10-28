import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechTermValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechCofaces

/-! # Cech Linear Factors -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechLinearFactors

noncomputable section

/-! The negative-twist factor maps as linear maps into the full localization modules. -/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def negativeTwistCechFactorMap (d q : ℕ)
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q) :
    Ordered.CoefficientCechTerms.coefficientCechFactor (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q a.val →ₗ[R]
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.ModuleChart R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a) :=
  (HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a) (-(d : ℤ))).subtype.comp (CechTermEquivalence.negativeTwistCechFactorEquiv I d q a).toLinearMap

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechLinearFactors
