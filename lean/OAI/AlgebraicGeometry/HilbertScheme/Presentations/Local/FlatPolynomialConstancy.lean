import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientFreeBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial
import Mathlib.RingTheory.Flat.LocallyFree

/-! # Flat Polynomial Constancy -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatPolynomialConstancy.GradedHilbert

noncomputable section

/-! Flat projective families over Noetherian local rings have the same
eventual Hilbert function after every nonzero coefficient extension. -/

open _root_.AlgebraicGeometry

universe u v
variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]

theorem localFlat_eventual_hilbertFunction_baseChange
    (A : Type v) [CommRing A] [Nontrivial A] [Algebra R A] :
    ∃ N : ℕ, ∀ d ≥ N,
      Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  obtain ⟨N, hN⟩ := Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.eventual_coordinatePieces_flat_of_projective_flat I
  refine ⟨N, fun d hd => ?_⟩
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := hN d hd
  let : Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := Module.free_of_flat_of_isLocalRing
  exact QuotientFreeBaseChange.GradedHilbert.degreeQuotient_finrank_baseChange_of_free_ring I d

theorem localFlat_hilbertPolynomial_baseChange_iff
    (A : Type v) [CommRing A] [Nontrivial A] [Algebra R A] (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal P ↔
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  obtain ⟨N, hN⟩ := localFlat_eventual_hilbertFunction_baseChange I A
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨max N D, fun d hd => ?_⟩
    rw [← hN d ((le_max_left _ _).trans hd)]
    exact hD d ((le_max_right _ _).trans hd)
  · rintro ⟨D, hD⟩
    refine ⟨max N D, fun d hd => ?_⟩
    rw [hN d ((le_max_left _ _).trans hd)]
    exact hD d ((le_max_right _ _).trans hd)

theorem localFlat_saturated_fiber_polynomial_iff
    (K : Type u) [Field K] [Algebra R K] (P : Polynomial ℚ) :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I)).toIdeal P ↔
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P :=
  (Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff _ P).trans
    (localFlat_hilbertPolynomial_baseChange_iff I K P)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Local.FlatPolynomialConstancy.GradedHilbert
