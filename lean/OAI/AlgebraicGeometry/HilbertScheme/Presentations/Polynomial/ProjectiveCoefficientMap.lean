import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.CoefficientMap
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientStructure

/-! # Projective Coefficient Map -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap.GradedHilbert

noncomputable section

/-! The actual coefficient morphism between polynomial projective spaces
and its compatibility with projective homogeneous quotient inclusions. -/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R S : Type u} [CommRing R] [CommRing S] {n : ℕ}

theorem polynomial_irrelevant_le_span_variables :
    (HomogeneousIdeal.irrelevant (Hilbert.Polynomial.GradedHilbert.grading R n)).toIdeal ≤
      Ideal.span (Set.range (X : Fin (n + 1) → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (Hilbert.Polynomial.GradedHilbert.grading R n)).mpr
  intro d hd f hf
  change f ∈ Ideal.span (Set.range (X : Fin (n + 1) → Hilbert.Polynomial.GradedHilbert.CoordinateRing R n))
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro a ha
  have had : a.degree = d := (Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f d).mp hf a ha
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! hzero
    have haz : a = 0 := Finsupp.ext hzero
    rw [haz] at had
    simp only [map_zero] at had
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Set.mem_univ i, hi⟩

theorem irrelevant_gradedCoefficient_le_map (φ : R →+* S) :
    HomogeneousIdeal.irrelevant (Hilbert.Polynomial.GradedHilbert.grading S n) ≤
      (HomogeneousIdeal.irrelevant (Hilbert.Polynomial.GradedHilbert.grading R n)).map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) := by
  change (HomogeneousIdeal.irrelevant (Hilbert.Polynomial.GradedHilbert.grading S n)).toIdeal ≤ _
  apply polynomial_irrelevant_le_span_variables.trans
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have he : Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ (X i) = X i := MvPolynomial.map_X φ i
  rw [← he]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem (Hilbert.Polynomial.GradedHilbert.grading R n)
    Nat.zero_lt_one (isHomogeneous_X R i))

def polynomialProjectiveCoefficientMap (φ : R →+* S) : Proj (Hilbert.Polynomial.GradedHilbert.grading S n) ⟶ Proj (Hilbert.Polynomial.GradedHilbert.grading R n) :=
  Proj.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ) (irrelevant_gradedCoefficient_le_map φ)

theorem polynomialProjectiveCoefficientMap_preimage (φ : R →+* S) (i : Fin (n + 1)) :
    polynomialProjectiveCoefficientMap (n := n) φ ⁻¹ᵁ Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading R n) (X i) =
      Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading S n) (X i) := by
  change Proj.basicOpen (Hilbert.Polynomial.GradedHilbert.grading S n) (Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ (X i)) = _
  rw [show Graded.BaseChange.GradedHilbert.gradedCoefficientMap φ (X i) = X i from MvPolynomial.map_X φ i]

theorem projectiveCoefficientMap_inclusion [Algebra R S] (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := S) I ≫ Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I =
      Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) ≫
        polynomialProjectiveCoefficientMap (algebraMap R S) := by
  have he : (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I).comp (Graded.Quotient.GradedHilbert.gradedQuotientMap I) =
      (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).comp
        (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R S)) := by
    ext f
    rfl
  change Proj.map (Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap I) (Quotient.CoefficientMap.GradedHilbert.irrelevant_quotientCoefficient_le_map I) ≫
      Proj.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I) =
    Proj.map (Graded.Quotient.GradedHilbert.gradedQuotientMap (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
      (Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) ≫
    Proj.map (Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R S)) (irrelevant_gradedCoefficient_le_map _)
  rw [← Proj.map_comp, ← Proj.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveCoefficientMap.GradedHilbert
