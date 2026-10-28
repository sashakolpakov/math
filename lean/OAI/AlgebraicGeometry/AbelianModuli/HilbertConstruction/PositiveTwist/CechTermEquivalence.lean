import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.ChartSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CechIntersectionCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms

/-! # Cech Term Equivalence -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechTermEquivalence

noncomputable section

/-! Actual nonnegative-twist projective Čech terms are linearly equivalent to the corresponding homogeneous localization terms. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def positiveTwistCechFactorEquiv (d q : ℕ)
    (a : Ordered.SectionCechIndices.OrderedCechIndex (ULift.{u} (Fin (n + 1))) q) :
    Ordered.CoefficientCechTerms.coefficientCechFactor (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
      (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q a.val ≃ₗ[R]
        HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
          (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a) (d : ℤ) := by
  let F := Coefficient.ModulePresheaf.schemeModulePresheaf (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf
  let e := F.mapIso (eqToIso (Projective.CechIntersectionCoordinates.projectiveCechIntersection_eq_chart I a).symm).op
  exact e.toLinearEquiv.trans (ChartSections.positiveTwistChartDegreeEquiv I d (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset a)
    (a.val 0).down (Projective.CechIntersectionCoordinates.projectiveCechIndexFinset_mem a 0))

def positiveTwistCechTermEquiv (d q : ℕ) :
    (((Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf).X q) ≃ₗ[R]
      HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) (q + 1) :=
  (Ordered.CoefficientCechTerms.orderedCoefficientCechObjectIsoPi
    (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q).toLinearEquiv.trans
      ((LinearEquiv.piCongrRight (fun a ↦ positiveTwistCechFactorEquiv I d q a)).trans
        ((LinearEquiv.piCongrLeft R
          (fun s : {s : Finset (Fin (n + 1)) // s.card = q + 1} ↦
            HilbertScheme.Presentations.Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s.val (d : ℤ))
          (OrderedCech.LiftedIndices.orderedCechLiftedFinsetEquiv (Fin (n + 1)) q)).trans
            (HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermEquiv R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
              (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (d : ℤ) (q + 1)).symm))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PositiveTwist.CechTermEquivalence
