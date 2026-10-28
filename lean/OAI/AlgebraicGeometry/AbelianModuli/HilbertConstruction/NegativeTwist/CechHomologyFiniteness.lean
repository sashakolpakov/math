import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechComplexIsomorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TwistedCoordinateCechFiniteness

/-! # Cech Homology Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechHomologyFiniteness

noncomputable section

/-! The Čech cohomology of every actual negative projective twist is finite. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
  (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem negativeTwistCech_homology_finite (d q : ℕ) :
    Module.Finite R (((Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj
      (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf).homology q) := by
  have := TwistedCoordinateCechFiniteness.twistedCoordinateCech_homology_finite I (-(d : ℤ)) q
  let e : (((Projective.CoefficientCechFunctor.projectiveCoefficientCechFunctor I).obj
      (Negative.ProjectiveTwistingBundle.negativeProjectiveTwistingBundle I d).sheaf).homology q) ≅
      ((Cochain.Head.CochainHead.tail (HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R
        (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) (-(d : ℤ)))).homology q) :=
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).mapIso
      (CechComplexIsomorphism.negativeTwistCechComplexIso I d)
  exact Module.Finite.equiv e.symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NegativeTwist.CechHomologyFiniteness
