import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.FamilyCoordinates
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.QuotientRankBaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Homogeneous.IdealTower

/-! # Fiber Function -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.FiberFunction

noncomputable section

/-! The recovered field fibers determine the high-degree coordinate ranks on the coefficient spectrum. -/

open _root_.AlgebraicGeometry

universe u

theorem coefficientFiber_rank_eq_polynomial
    {C A : Type u} [CommRing C] [IsNoetherianRing C] [CommRing A] [Algebra C A]
    {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading C n))
    [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))]
    (P : Polynomial ℚ) (q : PrimeSpectrum A)
    (hP : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := q.asIdeal.ResidueField)
        (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))).toIdeal P)
    (d : ℕ) (hd : HilbertScheme.Presentations.Flat.FamilyCoordinates.GradedHilbert.flatFamilyHilbertDegree I P ≤ d) :
    (Module.rankAtStalk (R := C) (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) (q.comap (algebraMap C A)) : ℚ) =
      P.eval (d : ℚ) := by
  let K := q.asIdeal.ResidueField
  let : Algebra C K := ((algebraMap A K).comp (algebraMap C A)).toAlgebra
  have : IsScalarTower C A K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let J := HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I
  have hdB : HilbertScheme.Presentations.Projective.FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound I ≤ d := (le_max_left _ _).trans hd
  have hdP : HilbertScheme.Presentations.Hilbert.Truncation.GradedHilbert.hilbertParameterDegree.{u} n P ≤ d := (le_max_right _ _).trans hd
  have : Module.Projective C (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d) := HilbertScheme.Presentations.Flat.FamilyCoordinates.GradedHilbert.coordinateBound_degreeQuotient_projective I d hdB
  have : Module.Projective A (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient J.toIdeal d) := (HilbertScheme.Presentations.Projective.FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound_spec I A d hdB).1
  have hr := HilbertScheme.Presentations.QuotientRankBaseChange.GradedHilbert.degreeQuotient_rankAtStalk_baseChange (A := A) I d q
  rw [HilbertScheme.Presentations.Relative.Coordinates.GradedHilbert.degreeQuotient_rankAtStalk] at hr
  rw [← hr]
  have hsat : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J)).toIdeal d =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J).toIdeal d := by
    change HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K)
      (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))).toIdeal d = _
    rw [HilbertScheme.Presentations.Homogeneous.IdealTower.GradedHilbert.extendedHomogeneousIdeal_tower]
    exact (HilbertScheme.Presentations.Projective.FamilyCoordinateBound.GradedHilbert.projectiveFamilyCoordinateBound_spec I K d hdB).2
  have he : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J).toIdeal d =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J)).toIdeal d :=
    (Submodule.quotEquivOfEq _ _ hsat.symm).finrank_eq
  rw [he]
  exact (HilbertScheme.Presentations.Hilbert.Truncation.GradedHilbert.hilbertParameterDegree_spec n P K (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) J))
    (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_isSaturated _) hP).2 d hdP

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.FiberFunction
