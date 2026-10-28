import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.SaturationBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Coordinate.FlatBaseChange

/-! # Family Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert

noncomputable section

/-! A single dimension-and-polynomial degree gives actual Grassmannian coordinates for all saturated flat projective families over noetherian bases. -/

open _root_.AlgebraicGeometry

universe u

def uniformHilbertFamilyDegree (n : ℕ) (P : Polynomial ℚ) : ℕ :=
  max (RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P) (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P)

variable {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ}
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (hSat : Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal)
variable [Flat (Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]
variable (P : Polynomial ℚ) (hP : ∀ p : PrimeSpectrum R,
  Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
    (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)

include hSat hP in
theorem uniformHilbertFamilyDegree_rankAtStalk (d : ℕ) (hd : uniformHilbertFamilyDegree.{u} n P ≤ d)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) p = (P.eval (d : ℚ)).num.toNat := by
  have hdB : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d := (le_max_left _ _).trans hd
  have hdP : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ d := (le_max_right _ _).trans hd
  let : Module.Flat R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_flat I hSat P hP d hdB
  rw [Relative.Coordinates.GradedHilbert.degreeQuotient_rankAtStalk]
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I
  have hsat := SaturationBaseChange.GradedHilbert.uniform_saturated_saturation_baseChange I hSat P hP p.asIdeal.ResidueField d hdB
  have he : Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal d :=
    (Submodule.quotEquivOfEq _ _ hsat.symm).finrank_eq
  rw [he]
  have hp := (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P p.asIdeal.ResidueField (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J)
    (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated J) (hP p)).2 d hdP
  rw [← hp]
  simp only [Rat.num_natCast, Int.toNat_natCast]

def uniformFlatFamilyHilbertGrassmannian (d : ℕ) (hd : uniformHilbertFamilyDegree.{u} n P ≤ d) :
    Module.Grassmannian R (Hilbert.Polynomial.GradedHilbert.grading R n d) (P.eval (d : ℚ)).num.toNat where
  toSubmodule := Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d
  finite_quotient := Hilbert.Polynomial.GradedHilbert.degreeQuotient_finite _ _
  projective_quotient := SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_projective I hSat P hP d ((le_max_left _ _).trans hd)
  rankAtStalk_eq := uniformHilbertFamilyDegree_rankAtStalk I hSat P hP d hd

include hSat hP in
theorem uniform_saturated_coordinate_all_baseChanges
    (S : Type u) [CommRing S] [Algebra R S] (d : ℕ) (hd : RegularCoordinateFlag.GradedHilbert.regularCoordinateFlagBound.{u} n P ≤ d) :
    Module.Projective S (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d) ∧
      Hilbert.Polynomial.GradedHilbert.degreeRelations (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).toIdeal d =
        Hilbert.Polynomial.GradedHilbert.degreeRelations (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal d := by
  let : Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := SaturatedCoordinates.GradedHilbert.uniform_saturated_coordinate_projective I hSat P hP d hd
  exact ⟨Coordinate.FlatBaseChange.GradedHilbert.degreeQuotient_projective_baseChange I d, SaturationBaseChange.GradedHilbert.uniform_saturated_saturation_baseChange I hSat P hP S d hd⟩

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Uniform.FamilyCoordinates.GradedHilbert
