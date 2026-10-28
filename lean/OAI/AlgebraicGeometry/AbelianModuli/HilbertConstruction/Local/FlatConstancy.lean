import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial
import Mathlib.RingTheory.Flat.LocallyFree
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Flat Constancy -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FlatConstancy

noncomputable section

/-! Over a noetherian local ring, a flat projective quotient has the same eventual Hilbert function after every field-valued coefficient extension. -/

open _root_.AlgebraicGeometry

universe u v

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] {n : ℕ}
variable (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]

theorem localFlat_eventual_fieldHilbertFunction (K : Type v) [Field K] [Algebra R K] :
    ∃ N : ℕ, ∀ d ≥ N,
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I).toIdeal d = HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d := by
  obtain ⟨N, hN⟩ := HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.eventual_coordinatePieces_flat_of_projective_flat I
  refine ⟨N, fun d hd => ?_⟩
  have : Module.Flat R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := hN d hd
  have : Module.Free R (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := Module.free_of_flat_of_isLocalRing
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  change Module.finrank K (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I).toIdeal d) = _
  rw [← (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := K) I d).finrank_eq]
  exact Module.finrank_baseChange

theorem localFlat_fieldHilbertPolynomial_iff (K : Type v) [Field K] [Algebra R K]
    (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P := by
  obtain ⟨N, hN⟩ := localFlat_eventual_fieldHilbertFunction I K
  constructor
  · rintro ⟨D, hD⟩
    refine ⟨max N D, fun d hd => ?_⟩
    rw [← hN d ((le_max_left _ _).trans hd)]
    exact hD d ((le_max_right _ _).trans hd)
  · rintro ⟨D, hD⟩
    refine ⟨max N D, fun d hd => ?_⟩
    rw [hN d ((le_max_left _ _).trans hd)]
    exact hD d ((le_max_right _ _).trans hd)

theorem localFlat_saturatedFieldHilbertPolynomial_iff (K : Type u) [Field K] [Algebra R K]
    (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I)).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial I.toIdeal P :=
  (HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff _ P).trans (localFlat_fieldHilbertPolynomial_iff I K P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.FlatConstancy
