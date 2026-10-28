import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCechFunctor

/-! # Coefficient Cech Bounded -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCechBounded

noncomputable section

/-! The projective coefficient Cech complex vanishes above the cover bound. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem projectiveCoefficientCech_bounded (M : (Proj (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)).Modules)
    (q : ℕ) (hq : n + 1 ≤ q) : IsZero (((CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj M).X q) :=
  Ordered.CoefficientCechComplex.orderedCoefficientCechObject_isZero_of_card_le _ M (CechCover.projectiveCechOpens I) q
    (by simpa only [Fintype.card_ulift, Fintype.card_fin] using hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientCechBounded
