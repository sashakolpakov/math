import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechDifferentialValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.GradedCechDifferential
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ModuleCechTermExt

/-! # Cech Differential Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechDifferentialCompatibility

noncomputable section

/-! The actual negative-twist Čech term equivalences commute with the full differentials. -/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem negativeTwistCechTermEquiv_differential (d q : ℕ)
    (x : (((Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf).X q)) :
    CechTermEquivalence.negativeTwistCechTermEquiv I d (q + 1)
      (Ordered.CoefficientCechComplex.orderedCoefficientCechDifferential (Coefficient.ModulePresheaf.schemeCoefficientMap (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
        (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf (Projective.CechCover.projectiveCechOpens I) q x) =
      HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTermDifferential (σ := Fin (n + 1)) R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
        (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (-(d : ℤ)) (q + 1) (CechTermEquivalence.negativeTwistCechTermEquiv I d q x) := by
  apply Projective.ModuleCechTermExt.projectiveModuleCechTerm_ext I (-(d : ℤ)) (q + 1)
  intro a
  exact (CechDifferentialValues.negativeTwistCechTermEquiv_differential_value I d q x a).trans
    (Projective.GradedCechDifferential.projectiveModuleCechDifferential_ordered I a (CechTermEquivalence.negativeTwistCechTermEquiv I d q x).val).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechDifferentialCompatibility
