import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.IntegerQuotient
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartModule
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCharts
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness

/-! # Projective Coordinate Pieces -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert

noncomputable section

/-!
Flat projective quotients over noetherian rings have flat homogeneous
coordinate pieces in sufficiently high degree.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.ChartModule.GradedModules OAI.AlgebraicGeometry.HilbertScheme.Presentations.EventualDegreeFlatness.ProjectiveCech

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem quotient_inversionMonomial_homogeneous
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (s : Finset (Fin (n + 1))) :
    algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (LaurentMonomials.ProjectiveCech.inversionMonomial R s) ∈ Graded.Quotient.GradedHilbert.quotientGrading I s.card := by
  apply (Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem
  have h := Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s
  rw [IntegerPolynomialGrading.GradedModules.polynomialIntegerGrading_nat] at h
  exact h

def coordinateChartModuleEquiv (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (s : Finset (Fin (n + 1))) :
    HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (LaurentMonomials.ProjectiveCech.inversionMonomial R s)) ≃ₗ[R]
        Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0 :=
  Homogeneous.ChartModule.GradedModules.homogeneousChartModuleEquiv (WeightedFreeModules.GradedModules.polynomialIntegerGrading R) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (Graded.Quotient.GradedHilbert.quotientGrading I) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading_nat I) (LaurentMonomials.ProjectiveCech.inversionMonomial R s) s.card
    (Graded.ModuleRestriction.ProjectiveCech.inversionMonomial_integer_degree R s) (quotient_inversionMonomial_homogeneous I s)

theorem coordinateChartDegreeZero_flat (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
    (s : Finset (Fin (n + 1))) (hs : s.Nonempty) :
    Module.Flat R (Graded.ModuleRestriction.ProjectiveCech.moduleChartDegree R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal)
      (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I) s 0) := by
  let : Module.Flat R (HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I)
      (algebraMap (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (LaurentMonomials.ProjectiveCech.inversionMonomial R s))) :=
    ProjectiveCharts.GradedHilbert.homogeneousChart_flat_of_projective_flat (Graded.Quotient.GradedHilbert.quotientGrading I) (Finset.card_pos.mpr hs)
      (quotient_inversionMonomial_homogeneous I s)
  exact Module.Flat.of_linearEquiv (coordinateChartModuleEquiv I s).symm

theorem eventual_coordinatePieces_flat_of_projective_flat [IsNoetherianRing R]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ N : ℕ, ∀ d ≥ N, Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  obtain ⟨N, hN⟩ := EventualDegreeFlatness.ProjectiveCech.eventual_degree_flat_of_projective_charts
    (σ := Fin (n + 1)) R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I)
    (coordinateChartDegreeZero_flat I)
  refine ⟨N, fun d hd => ?_⟩
  let : Module.Flat R (Coordinate.IntegerQuotient.GradedHilbert.integerQuotientGrading I (d : ℤ)) := hN d (by exact_mod_cast hd)
  exact Module.Flat.of_linearEquiv (Coordinate.IntegerQuotient.GradedHilbert.integerDegreeQuotientEquiv I d)

theorem projectiveQuotient_flat_iff_eventual_coordinatePieces_flat [IsNoetherianRing R]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) ↔
      ∃ N : ℕ, ∀ d ≥ N, Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  constructor
  · intro h
    let : Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)) := h
    exact eventual_coordinatePieces_flat_of_projective_flat I
  · rintro ⟨N, hN⟩
    exact Projective.Flatness.GradedHilbert.projectiveQuotient_flat_of_eventually_flat I N hN

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert
