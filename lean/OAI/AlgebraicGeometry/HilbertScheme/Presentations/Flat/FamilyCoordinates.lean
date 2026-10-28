import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.FamilyCoordinateBound
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Relative.Coordinates

/-! # Family Coordinates -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.FamilyCoordinates.GradedHilbert

noncomputable section

/-!
Grassmannian coordinates for actual flat projective quotients. Saturation
of residue-field coordinate ideals is proved unnecessary: their projective
saturations determine the polynomial and agree in the constructed high degrees.
-/

open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem extendedHomogeneousIdeal_self (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I = I := by
  apply HomogeneousIdeal.ext
  change Ideal.map (MvPolynomial.map (algebraMap R R)) I.toIdeal = I.toIdeal
  have hm : MvPolynomial.map (algebraMap R R) = RingHom.id (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) := by
    apply RingHom.ext
    intro f
    exact MvPolynomial.map_id f
  rw [hm, Ideal.map_id]

variable [IsNoetherianRing R]
variable (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) [Flat (Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I))]

theorem coordinateBound_degreeQuotient_projective (d : ℕ) (hd : Presentations.Projective.FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound I ≤ d) :
    Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := by
  let : Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := R) I).toIdeal d) :=
    (Presentations.Projective.FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound_spec I R d hd).1
  exact Module.Projective.of_equiv (Submodule.quotEquivOfEq _ _
    (congrArg (fun J : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) => Hilbert.Polynomial.GradedHilbert.degreeRelations J.toIdeal d)
      (extendedHomogeneousIdeal_self I)))

def flatFamilyHilbertDegree (P : Polynomial ℚ) : ℕ :=
  max (Presentations.Projective.FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound I) (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P)

theorem flatFamilyHilbertDegree_rankAtStalk (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R,
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
        (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
    (d : ℕ) (hd : flatFamilyHilbertDegree I P ≤ d) (p : PrimeSpectrum R) :
    Module.rankAtStalk (R := R) (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) p = (P.eval (d : ℚ)).num.toNat := by
  have hdB : Presentations.Projective.FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound I ≤ d := (le_max_left _ _).trans hd
  have hdP : Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ d := (le_max_right _ _).trans hd
  let : Module.Projective R (Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := coordinateBound_degreeQuotient_projective I d hdB
  rw [Relative.Coordinates.GradedHilbert.degreeQuotient_rankAtStalk]
  let J := Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I
  have hsat := (Presentations.Projective.FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound_spec I p.asIdeal.ResidueField d hdB).2
  have he : Hilbert.Polynomial.GradedHilbert.hilbertFunction J.toIdeal d = Hilbert.Polynomial.GradedHilbert.hilbertFunction (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J).toIdeal d :=
    (Submodule.quotEquivOfEq _ _ hsat.symm).finrank_eq
  rw [he]
  have hp := (Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P p.asIdeal.ResidueField (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation J)
    (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated J) (hP p)).2 d hdP
  rw [← hp]
  simp only [Rat.num_natCast, Int.toNat_natCast]

def flatFamilyHilbertGrassmannian (P : Polynomial ℚ)
    (hP : ∀ p : PrimeSpectrum R,
      Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
        (Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := p.asIdeal.ResidueField) I)).toIdeal P)
    (d : ℕ) (hd : flatFamilyHilbertDegree I P ≤ d) :
    Module.Grassmannian R (Hilbert.Polynomial.GradedHilbert.grading R n d) (P.eval (d : ℚ)).num.toNat where
  toSubmodule := Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d
  finite_quotient := Hilbert.Polynomial.GradedHilbert.degreeQuotient_finite _ _
  projective_quotient := coordinateBound_degreeQuotient_projective I d ((le_max_left _ _).trans hd)
  rankAtStalk_eq := flatFamilyHilbertDegree_rankAtStalk I P hP d hd

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.FamilyCoordinates.GradedHilbert
