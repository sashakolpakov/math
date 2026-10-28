import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cochain.FiniteCycles
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Finite.GradedCechHomology
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Cech.AugmentationMap

/-! # Cech Complex -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechComplex

noncomputable section

/-! The nonaugmented homogeneous Čech complex of a flat projective coordinate quotient is bounded, termwise flat, and has finite cohomology over a Noetherian base. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

def coordinateNonnegativeCechComplex : CochainComplex (ModuleCat.{u} R) ℕ :=
  Cochain.Head.CochainHead.tail (HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0)

theorem coordinateNonnegativeCechComplex_bounded (q : ℕ) (hq : n + 1 ≤ q) :
    IsZero ((coordinateNonnegativeCechComplex I).X q) := by
  have : Subsingleton ((coordinateNonnegativeCechComplex I).X q) :=
    HilbertScheme.Presentations.Bounded.ModuleCechHomology.ProjectiveCech.moduleCechTerm_subsingleton_of_bounded R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 (q + 1) (by simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hq)
  exact ModuleCat.isZero_of_subsingleton _

theorem coordinateNonnegativeCechComplex_flat
    [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))] (q : ℕ) :
    Module.Flat R ((coordinateNonnegativeCechComplex I).X q) :=
  HilbertScheme.Presentations.ModuleCech.Terms.ProjectiveCech.moduleCechTerm_flat R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 (q + 1)
    (Nat.succ_pos q) (HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.coordinateChartDegreeZero_flat I)

theorem coordinateNonnegativeCechComplex_homology_finite [IsNoetherianRing R] (q : ℕ) :
    Module.Finite R ((coordinateNonnegativeCechComplex I).homology q) := by
  let C := HilbertScheme.Presentations.ModuleCech.CechComplex.ProjectiveCech.moduleCechComplex (σ := Fin (n + 1)) R
    (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0
  cases q with
  | zero =>
    have : Module.Finite R (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (0 : ℤ)) :=
      Module.Finite.equiv (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I 0)
    have : Module.Finite R (C.X 0) := Module.Finite.equiv
      (HilbertScheme.Presentations.Cech.AugmentationDegree.ProjectiveCech.moduleCechAugmentationEquiv (σ := Fin (n + 1)) R
        (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0).symm
    have : Module.Finite R (C.homology 1) := HilbertScheme.Presentations.Finite.GradedCechHomology.ProjectiveCech.moduleCech_homology_finite R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 0
    exact Cochain.FiniteCycles.cochain_tail_zero_homology_finite C
  | succ q =>
    have : Module.Finite R (C.homology (q + 2)) := HilbertScheme.Presentations.Finite.GradedCechHomology.ProjectiveCech.moduleCech_homology_finite R
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (HilbertScheme.Presentations.Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) 0 (q + 1)
    exact Module.Finite.equiv (Cochain.HeadCohomology.CochainHead.tailHomologyIso C q).symm.toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coordinate.CechComplex
