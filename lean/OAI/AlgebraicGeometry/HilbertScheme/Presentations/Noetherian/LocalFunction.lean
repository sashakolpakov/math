import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyGeneration
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientFreeBaseChange

/-! # Local Function -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalFunction.GradedHilbert

noncomputable section

/-! Uniform coordinate ranks over local noetherian bases, computed from
the actual saturated residue-fiber Hilbert polynomials. -/

open _root_.AlgebraicGeometry

universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hI : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R, Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
  (Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
include hI hP

theorem uniformLocal_degreeQuotient_free (d : ℕ) (hd : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ d) :
    Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) :=
    Uniform.SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_flat I hI P hP d ((le_max_left _ _).trans hd)
  exact Module.free_of_flat_of_isLocalRing

theorem uniformLocal_hilbertFunction (d : ℕ) (hd : Uniform.FamilyCoordinates.GradedHilbert.uniformHilbertFamilyDegree.{u} n P ≤ d) :
    (Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d : ℚ) = P.eval (d : ℚ) := by
  let p : PrimeSpectrum R := IsLocalRing.closedPoint R
  let K := p.asIdeal.ResidueField
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I
  let : Module.Free R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := uniformLocal_degreeQuotient_free I hI P hP d hd
  have hR : Hilbert.Polynomial.GradedHilbert.hilbertFunction I.toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal d :=
    (ValuationClosureFunction.GradedHilbert.degreeQuotient_finrank_baseChange_of_free (L := K) I d).symm
  have hrel := Uniform.SaturationBaseChange.GradedHilbert.uniform_saturated_saturation_baseChange I hI P hP K d ((le_max_left _ _).trans hd)
  have hK : Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction (Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal d :=
    (Submodule.quotEquivOfEq _ _ hrel.symm).finrank_eq
  rw [hR, hK]
  exact (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K (Projective.Saturation.GradedHilbert.projectiveSaturation J)
    (Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated J) (hP p)).2 d ((le_max_right _ _).trans hd)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Noetherian.LocalFunction.GradedHilbert
