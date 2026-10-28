import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientRankBaseChange

/-! # Noetherian Field Polynomial -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.NoetherianFieldPolynomial.GradedHilbert

noncomputable section

/-! Canonical residue polynomials of a saturated flat projective family
over a noetherian ring determine every field-valued coefficient fiber. -/

open _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
  (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
include hI hP

theorem uniformFamily_field_hilbertFunction (K : Type u) [Field K] [Algebra R K]
    (d : ℕ) (hd : FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ d) :
    (Hilbert.Polynomial.GradedHilbert.hilbertFunction (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I).toIdeal d : ℚ) = P.eval (d : ℚ) := by
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :=
    SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_flat I hI P hP d ((le_max_left _ _).trans hd)
  let p := (IsLocalRing.closedPoint K).comap (algebraMap R K)
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I
  have hrel := SaturationBaseChange.GradedHilbert.uniform_saturated_saturation_baseChange I hI P hP p.asIdeal.ResidueField d ((le_max_left _ _).trans hd)
  have he : Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction (Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal d :=
    (Submodule.quotEquivOfEq _ _ hrel.symm).finrank_eq
  rw [QuotientRankBaseChange.GradedHilbert.degreeQuotient_field_hilbertFunction (K := K) I d, he]
  exact (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P p.asIdeal.ResidueField (Projective.Saturation.GradedHilbert.projectiveSaturation J)
    (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated J) (hP p)).2 d ((le_max_right _ _).trans hd)

theorem uniformFamily_field_hasHilbertPolynomial (K : Type u) [Field K] [Algebra R K] :
    Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I)).toIdeal P := by
  apply (Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff _ P).mpr
  exact ⟨FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P, uniformFamily_field_hilbertFunction I hI P hP K⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.NoetherianFieldPolynomial.GradedHilbert
