import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Graded.BaseChange
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Flatness

/-! # Coefficient Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.CoefficientMap.GradedHilbert

noncomputable section

/-!
The graded coefficient map on homogeneous quotient rings, and the
resulting morphism of projective schemes after base change.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S] {n : ℕ}

def quotientCoefficientMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Graded.Quotient.GradedHilbert.quotientGrading I →+*ᵍ Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) where
  __ := Ideal.quotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal
    (MvPolynomial.map (algebraMap R S)) Ideal.le_comap_map
  map_mem h := by
    obtain ⟨f, hf, rfl⟩ := h
    exact ⟨MvPolynomial.map (algebraMap R S) f, hf.map (algebraMap R S), rfl⟩

theorem quotientCoefficientMap_mk (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (f : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) :
    quotientCoefficientMap (S := S) I (Graded.Quotient.GradedHilbert.gradedQuotientMap I f) =
      Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (MvPolynomial.map (algebraMap R S) f) := rfl

theorem quotientCoefficientMap_X (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    quotientCoefficientMap (S := S) I (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) =
      Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i) := by
  rw [quotientCoefficientMap_mk, MvPolynomial.map_X]

theorem irrelevant_quotientCoefficient_le_map (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    HomogeneousIdeal.irrelevant (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) ≤
      (HomogeneousIdeal.irrelevant (Graded.Quotient.GradedHilbert.quotientGrading I)).map (quotientCoefficientMap (S := S) I) := by
  change (HomogeneousIdeal.irrelevant (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))).toIdeal ≤ _
  apply (Projective.Flatness.GradedHilbert.quotient_irrelevant_le_span_variables (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).trans
  apply Ideal.span_le.mpr
  rintro f ⟨i, rfl⟩
  change Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i) ∈
    Ideal.map (quotientCoefficientMap (S := S) I) (HomogeneousIdeal.irrelevant (Graded.Quotient.GradedHilbert.quotientGrading I)).toIdeal
  rw [← quotientCoefficientMap_X (S := S) I i]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem (Graded.Quotient.GradedHilbert.quotientGrading I)
    Nat.zero_lt_one ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i)))

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.CoefficientMap.GradedHilbert
