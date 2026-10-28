import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Quotient.CoefficientMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.ChartCoefficientMap

/-! # Coefficient Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert

noncomputable section

/-!
The actual morphism of projective quotients induced by a coefficient-ring
extension, and its standard-chart preimages.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

def projectiveCoefficientMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Quotient.GradedHilbert.projectiveQuotient (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) ⟶ Quotient.GradedHilbert.projectiveQuotient I :=
  Proj.map (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap I) (Quotient.CoefficientMap.GradedHilbert.irrelevant_quotientCoefficient_le_map I)

theorem projectiveCoefficientMap_preimage (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (i : Fin (n + 1)) :
    projectiveCoefficientMap (S := S) I ⁻¹ᵁ Proj.basicOpen (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) =
      Proj.basicOpen (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
        (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i)) := by
  change Proj.basicOpen (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
    (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))) = _
  rw [Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap_X]

theorem quotientCoefficientMap_algebraMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (r : R) :
    Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I (algebraMap R (Hilbert.Polynomial.GradedHilbert.CoordinateRing R n ⧸ I.toIdeal) r) =
      algebraMap S (Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
        (algebraMap R S r) := by
  change Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)
      (MvPolynomial.map (algebraMap R S) (C r)) =
    Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (C (algebraMap R S r))
  rw [MvPolynomial.map_C]

theorem projectiveCoefficientMap_away_aux (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1))
    (t : Hilbert.Polynomial.GradedHilbert.CoordinateRing S n ⧸ (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I).toIdeal)
    (ht : Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i)) = t) :
    Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) t
        (ht ▸ (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I).map_mem
          ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i))) Nat.zero_lt_one ≫
        projectiveCoefficientMap (S := S) I =
      Spec.map (CommRingCat.ofHom (HomogeneousLocalization.map (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I)
        (P := Submonoid.powers (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))) (Q := Submonoid.powers t)
          (by rintro _ ⟨k, rfl⟩; exact ⟨k, by rw [map_pow, ht]⟩))) ≫
        Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
          ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i)) Nat.zero_lt_one := by
  subst t
  exact Proj.awayι_comp_map (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I)
    (Quotient.CoefficientMap.GradedHilbert.irrelevant_quotientCoefficient_le_map I) Nat.zero_lt_one (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
      ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i))

theorem projectiveCoefficientMap_away (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) (i : Fin (n + 1)) :
    Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
        (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) (X i))
        ((Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).map_mem (isHomogeneous_X S i))
        Nat.zero_lt_one ≫ projectiveCoefficientMap (S := S) I =
      Spec.map (CommRingCat.ofHom (ChartCoefficientMap.GradedHilbert.chartCoefficientMap (S := S) I i)) ≫
        Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
          ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i)) Nat.zero_lt_one :=
  projectiveCoefficientMap_away_aux I i _ (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap_X I i)

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert
