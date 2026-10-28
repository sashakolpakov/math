import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientRankBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial

/-! # Flat Fiber Polynomial Specialization -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatFiberPolynomialSpecialization.PolarizationEmbedding

noncomputable section

/-! Every field specialization of a flat projective family has exactly
the Hilbert polynomial of its image residue point. -/

open _root_.AlgebraicGeometry

universe u v
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]

theorem field_hilbertPolynomial_iff_residue
    {K : Type v} [Field K] (φ : R →+* K) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal
        (S := ((IsLocalRing.closedPoint K).comap φ).asIdeal.ResidueField) I).toIdeal P := by
  let := φ.toAlgebra
  obtain ⟨N, hN⟩ := HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces.GradedHilbert.eventual_coordinatePieces_flat_of_projective_flat I
  have he (d : ℕ) (hd : N ≤ d) :
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ)).toIdeal d =
        HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal
          (S := ((IsLocalRing.closedPoint K).comap φ).asIdeal.ResidueField) I).toIdeal d := by
    let := hN d hd
    exact HilbertScheme.Presentations.QuotientRankBaseChange.GradedHilbert.degreeQuotient_field_hilbertFunction (K := K) I d
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨max a N, fun d hd => ?_⟩
    rw [← he d ((le_max_right _ _).trans hd)]
    exact ha d ((le_max_left _ _).trans hd)
  · rintro ⟨a, ha⟩
    refine ⟨max a N, fun d hd => ?_⟩
    rw [he d ((le_max_right _ _).trans hd)]
    exact ha d ((le_max_left _ _).trans hd)

theorem saturated_field_hilbertPolynomial_iff_residue
    {K : Type v} [Field K] (φ : R →+* K) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (I.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ))).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal
        (S := ((IsLocalRing.closedPoint K).comap φ).asIdeal.ResidueField) I).toIdeal P :=
  (HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff _ P).trans
    (field_hilbertPolynomial_iff_residue I φ P)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FlatFiberPolynomialSpecialization.PolarizationEmbedding
