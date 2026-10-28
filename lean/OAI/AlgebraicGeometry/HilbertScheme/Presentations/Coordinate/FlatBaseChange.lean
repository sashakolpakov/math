import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Coordinates

/-! # Flat Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.FlatBaseChange.GradedHilbert

noncomputable section

/-! The bound for flat coordinate pieces persists under arbitrary coefficient-ring base change. -/

open _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

theorem degreeQuotient_flat_baseChange (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (d : ℕ) [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    Module.Flat S (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d) :=
  Module.Flat.of_linearEquiv (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := S) I d).symm

theorem degreeQuotient_projective_baseChange (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (d : ℕ) [Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    Module.Projective S (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d) :=
  Module.Projective.of_equiv (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := S) I d)

theorem projectiveQuotient_eventual_flat_all_baseChanges [IsNoetherianRing R]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ N : ℕ, ∀ (S : Type u) [CommRing S] [Algebra R S], ∀ d ≥ N,
      Module.Flat S (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d) := by
  obtain ⟨N, hN⟩ := Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.eventual_coordinatePieces_flat_of_projective_flat I
  refine ⟨N, fun S _ _ d hd => ?_⟩
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := hN d hd
  exact degreeQuotient_flat_baseChange I d

theorem projectiveQuotient_eventual_projective_all_baseChanges [IsNoetherianRing R]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))] :
    ∃ N : ℕ, ∀ (S : Type u) [CommRing S] [Algebra R S], ∀ d ≥ N,
      Module.Projective S (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d) := by
  obtain ⟨N, hN⟩ := Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.eventual_coordinatePieces_flat_of_projective_flat I
  refine ⟨N, fun S _ _ d hd => ?_⟩
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := hN d hd
  let : Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := Relative.Coordinates.GradedHilbert.degreeQuotient_projective_of_flat I d
  exact degreeQuotient_projective_baseChange I d

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.FlatBaseChange.GradedHilbert
