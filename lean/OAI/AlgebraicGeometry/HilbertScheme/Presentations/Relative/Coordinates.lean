import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Hilbert.Truncation
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Noetherian.Basic

/-! # Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Coordinates.GradedHilbert

noncomputable section

/-!
Relative Grassmannian coordinates of homogeneous ideals. Residue-field
fibers determine the rank of each degree quotient; over a noetherian ring
a flat degree quotient is finite projective. The flatness input here is
degreewise module flatness, and must still be obtained for high-degree
sections of the geometric Hilbert families.
-/

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem degreeQuotient_rankAtStalk (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (d : ℕ) [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) p =
      Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal d := by
  rw [Module.rankAtStalk_eq]
  exact (Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := p.asIdeal.ResidueField) I d).finrank_eq

theorem degreeQuotient_projective_of_flat [IsNoetherianRing R]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  have : Module.FinitePresentation R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :=
    Module.finitePresentation_of_finite R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)
  exact Module.Flat.projective_of_finitePresentation

theorem hilbertParameterDegree_rankAtStalk (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (P : Polynomial ℚ)
    (hSat : ∀ p : PrimeSpectrum R,
      Hilbert.Polynomial.GradedHilbert.IsSaturated (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal)
    (hP : ∀ p : PrimeSpectrum R,
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal P)
    (d : ℕ) (hd : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ d)
    [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) p = (P.eval (d : ℚ)).num.toNat := by
  rw [degreeQuotient_rankAtStalk]
  have h := (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P p.asIdeal.ResidueField
    (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I) (hSat p) (hP p)).2 d hd
  rw [← h]
  simp only [Rat.num_natCast, Int.toNat_natCast]

/-- An actual relative Grassmannian point whenever the chosen degree
quotient is flat and the geometric polynomial conditions hold on fibers. -/
def relativeHilbertGrassmannian [IsNoetherianRing R]
    (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (P : Polynomial ℚ)
    (hSat : ∀ p : PrimeSpectrum R,
      Hilbert.Polynomial.GradedHilbert.IsSaturated (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal)
    (hP : ∀ p : PrimeSpectrum R,
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I).toIdeal P)
    (d : ℕ) (hd : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ d)
    [Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d)] :
    Module.Grassmannian R (Hilbert.Polynomial.GradedHilbert.grading R n d) (P.eval (d : ℚ)).num.toNat where
  toSubmodule := Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d
  finite_quotient := Hilbert.Polynomial.GradedHilbert.degreeQuotient_finite _ _
  projective_quotient := degreeQuotient_projective_of_flat I d
  rankAtStalk_eq := hilbertParameterDegree_rankAtStalk I P hSat hP d hd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Coordinates.GradedHilbert
