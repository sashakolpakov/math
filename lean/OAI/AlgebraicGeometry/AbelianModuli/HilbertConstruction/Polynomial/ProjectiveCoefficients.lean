import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.QuotientZero

/-! # Projective Coefficients -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.ProjectiveCoefficients

noncomputable section

/-!
Polynomial coefficient maps induce actual projective-space morphisms.
Homogeneous quotient inclusions commute with these coefficient maps.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem polynomial_irrelevant_le_variables :
    (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).mpr
  intro d hd p hp
  change p ∈ Ideal.span (Set.range (MvPolynomial.X : Fin (n + 1) → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n))
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro a ha
  have had : a.degree = d := (HilbertScheme.Presentations.Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support p d).mp hp a ha
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! hzero
    have haz : a = 0 := Finsupp.ext hzero
    rw [haz] at had
    simp only [map_zero] at had
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Set.mem_univ i, hi⟩

theorem polynomial_irrelevant_coefficient : HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) ≤
    (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R A)) := by
  change (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n)).toIdeal ≤ _
  apply (polynomial_irrelevant_le_variables (R := A)).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h := Ideal.mem_map_of_mem (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (n := n) (algebraMap R A)).toRingHom
    (HomogeneousIdeal.mem_irrelevant_of_mem (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) Nat.zero_lt_one (MvPolynomial.isHomogeneous_X R i))
  change MvPolynomial.X i ∈
    Ideal.map (MvPolynomial.map (algebraMap R A)) (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).toIdeal
  change MvPolynomial.map (algebraMap R A) (MvPolynomial.X i) ∈
    Ideal.map (MvPolynomial.map (algebraMap R A)) (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).toIdeal at h
  rw [MvPolynomial.map_X] at h
  exact h

def polynomialProjectiveCoefficientMap : Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading A n) ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) :=
  Proj.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R A)) polynomial_irrelevant_coefficient

theorem projectiveQuotientInclusion_coefficient (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) ≫
      polynomialProjectiveCoefficientMap =
        HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := A) I ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I := by
  change Proj.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)) _ ≫
    Proj.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R A)) _ =
      Proj.map (HilbertScheme.Presentations.Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := A) I) _ ≫ Proj.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) _
  rw [← Proj.map_comp, ← Proj.map_comp]
  have he : (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).comp
      (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R A)) =
        (HilbertScheme.Presentations.Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := A) I).comp (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) := by
    apply GradedRingHom.ext
    intro p
    rfl
  simp only [he]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.ProjectiveCoefficients
