import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegerCoordinateDegreeFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FiniteCycles
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedCechHomology
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.AugmentationMap

/-! # Twisted Coordinate Cech Finiteness -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TwistedCoordinateCechFiniteness

noncomputable section

/-! Nonaugmented coordinate Čech complexes have finite cohomology in every internal degree. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
  (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem twistedCoordinateCech_homology_finite (d : ℤ) (q : ℕ) :
    Module.Finite R ((Cochain.Head.CochainHead.tail (HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d)).homology q) := by
  let C := HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d
  cases q with
  | zero =>
    have : Module.Finite R (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I d) := IntegerCoordinateDegreeFiniteness.integerQuotientGrading_finite I d
    have : Module.Finite R (C.X 0) := Module.Finite.equiv
      (HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := Fin (n + 1)) R
        (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d).symm
    have : Module.Finite R (C.homology 1) := HilbertScheme.Presentations.Finite.GradedCechHomology.ProjectiveCech.moduleCech_homology_finite R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d 0
    exact Cochain.FiniteCycles.cochain_tail_zero_homology_finite C
  | succ q =>
    have : Module.Finite R (C.homology (q + 2)) := HilbertScheme.Presentations.Finite.GradedCechHomology.ProjectiveCech.moduleCech_homology_finite R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) d (q + 1)
    exact Module.Finite.equiv (Cochain.HeadCohomology.CochainHead.tailHomologyIso C q).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TwistedCoordinateCechFiniteness
