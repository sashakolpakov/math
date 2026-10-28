import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.CoordinateChangeEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GradedLinearCoordinateIsomorphism
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial

/-! # Coordinate Ideals -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateIdeals

noncomputable section

/-! Invertible polynomial-coordinate substitutions preserve
saturation and all homogeneous degree quotients. The quotient
comparison persists under arbitrary coefficient extension. -/
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ}
variable (e : (Fin (n + 1) →₀ R) ≃ₗ[R] (Fin (n + 1) →₀ R))

def polynomialLinearAlgEquiv : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ≃ₐ[R] HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n where
  __ := CoordinateSubstitution.polynomialLinearSubstitution e.toLinearMap
  invFun := CoordinateSubstitution.polynomialLinearSubstitution e.symm.toLinearMap
  left_inv p := DFunLike.congr_fun (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap_inverse e) p
  right_inv p := DFunLike.congr_fun (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap_inverse e.symm) p

def linearCoordinateIdeal (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) :=
  I.comap (GradedLinearCoordinateIsomorphism.gradedLinearCoordinateMap e.toLinearMap)

theorem linearCoordinateIdeal_mem (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (p : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    p ∈ (linearCoordinateIdeal e I).toIdeal ↔ polynomialLinearAlgEquiv e p ∈ I.toIdeal := Iff.rfl

theorem linearCoordinateIdeal_saturated (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (hI : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated I.toIdeal) : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.IsSaturated (linearCoordinateIdeal e I).toIdeal := by
  intro p d hp h
  apply hI (polynomialLinearAlgEquiv e p) d (CoordinateSubstitution.polynomialLinearSubstitution_homogeneous _ hp)
  obtain ⟨m, hm⟩ := h
  refine ⟨m, fun g hg => ?_⟩
  have H := hm ((polynomialLinearAlgEquiv e).symm g)
    (CoordinateSubstitution.polynomialLinearSubstitution_homogeneous e.symm.toLinearMap hg)
  change polynomialLinearAlgEquiv e ((polynomialLinearAlgEquiv e).symm g * p) ∈ I.toIdeal at H
  simpa only [map_mul, AlgEquiv.apply_symm_apply] using H

theorem linearCoordinateIdeal_degreeRelations (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations (linearCoordinateIdeal e I).toIdeal d =
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d).comap (HilbertConstruction.Polynomial.CoordinateChangeEvaluation.polynomialLinearDegreeEquiv e d).toLinearMap := rfl

def linearCoordinateIdealDegreeQuotientEquiv (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient (linearCoordinateIdeal e I).toIdeal d ≃ₗ[R] HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient I.toIdeal d :=
  Submodule.Quotient.equiv _ _ (HilbertConstruction.Polynomial.CoordinateChangeEvaluation.polynomialLinearDegreeEquiv e d) (by
    rw [linearCoordinateIdeal_degreeRelations]
    exact Submodule.map_comap_eq_of_surjective (HilbertConstruction.Polynomial.CoordinateChangeEvaluation.polynomialLinearDegreeEquiv e d).surjective
      (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.degreeRelations I.toIdeal d))

def linearCoordinateIdealExtendedDegreeEquiv
    (A : Type u) [CommRing A] [Algebra R A] (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (d : ℕ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (linearCoordinateIdeal e I)).toIdeal d ≃ₗ[A]
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.DegreeQuotient (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d :=
  (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := A) (linearCoordinateIdeal e I) d).symm.trans
    (((linearCoordinateIdealDegreeQuotientEquiv e I d).baseChange R A).trans
      (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.degreeQuotientBaseChangeEquiv (S := A) I d))

theorem linearCoordinateIdealExtended_hilbertPolynomial_iff
    (A : Type u) [CommRing A] [Algebra R A] (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (linearCoordinateIdeal e I)).toIdeal P ↔
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal P := by
  have H (d : ℕ) : HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (linearCoordinateIdeal e I)).toIdeal d =
      HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.hilbertFunction (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I).toIdeal d :=
    (linearCoordinateIdealExtendedDegreeEquiv e A I d).finrank_eq
  simp only [HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial, H]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Linear.CoordinateIdeals
