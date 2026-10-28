import OAI.AlgebraicGeometry.Resolution.Blowups.ProjectiveIsomorphism
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange

/-! # Polynomial Projective Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialProjectiveBaseChange.Construction

noncomputable section

/-! Actual polynomial projective space commutes with coefficient base change. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.MvPolynomial
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

theorem polynomial_irrelevant_le_span_variables :
    (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).toIdeal ≤
      Ideal.span (Set.range (X : Fin (n + 1) → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n)) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).mpr
  intro d hd f hf
  change f ∈ Ideal.span (Set.range (X : Fin (n + 1) → HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.CoordinateRing R n))
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro a ha
  have had : a.degree = d := (HilbertScheme.Presentations.Hilbert.MonomialBasis.GradedHilbert.mem_degreeSpace_iff_support f d).mp hf a ha
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! hzero
    have haz : a = 0 := Finsupp.ext hzero
    rw [haz] at had
    simp only [map_zero] at had
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Set.mem_univ i, hi⟩

theorem polynomial_coefficient_irrelevant_le_map :
    HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading S n) ≤
      (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).map
        (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R S)) := by
  change (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading S n)).toIdeal ≤ _
  apply polynomial_irrelevant_le_span_variables.trans
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change X i ∈ Ideal.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R S))
    (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).toIdeal
  have h := Ideal.mem_map_of_mem (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R S))
    (HomogeneousIdeal.mem_irrelevant_of_mem (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) Nat.zero_lt_one
      (isHomogeneous_X R i))
  change MvPolynomial.map (algebraMap R S) (X i) ∈
    Ideal.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R S))
      (HomogeneousIdeal.irrelevant (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)).toIdeal at h
  simpa only [MvPolynomial.map_X] using h

/-- Change only the coefficients of projective coordinates. -/
def polynomialProjectiveCoefficientMap : Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading S n) ⟶ Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) :=
  Proj.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R S)) polynomial_coefficient_irrelevant_le_map

theorem projectiveQuotientInclusion_over (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) =
      HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) := by
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient]
  unfold HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap
  rw [← Category.assoc, Blowup.BaseOpen.Construction.projMap_toSpecZero, Category.assoc, ← Spec.map_comp]
  congr 1

theorem projectiveQuotientInclusion_isIso_of_eq_bot (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (hI : I.toIdeal = ⊥) : IsIso (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) := by
  apply ProjectiveIsomorphism.Construction.projMap_isIso_of_bijective
  constructor
  · change Function.Injective (Ideal.Quotient.mk I.toIdeal)
    rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, hI]
  · exact Ideal.Quotient.mk_surjective

theorem projectiveQuotientInclusion_coefficient (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := S) I ≫ HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) ≫
        polynomialProjectiveCoefficientMap := by
  dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient]
  unfold HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion polynomialProjectiveCoefficientMap
  rw [← Proj.map_comp, ← Proj.map_comp]
  have he : (HilbertScheme.Presentations.Quotient.CoefficientMap.GradedHilbert.quotientCoefficientMap (S := S) I).comp (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) =
      (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).comp
        (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R S)) := by
    ext f
    rfl
  simp only [he]

/-- The ordinary polynomial Proj is the scheme-theoretic base change of
projective space over the original coefficient ring. -/
theorem polynomialProjective_isPullback :
    IsPullback (polynomialProjectiveCoefficientMap (R := R) (S := S) (n := n))
      (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading S n)) (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) := ⊥
  let J := HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I
  have hI : I.toIdeal = ⊥ := rfl
  have hJ : J.toIdeal = ⊥ := by
    change I.toIdeal.map (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.gradedCoefficientMap (algebraMap R S)) = ⊥
    rw [hI, Ideal.map_bot]
  let := projectiveQuotientInclusion_isIso_of_eq_bot I hI
  let := projectiveQuotientInclusion_isIso_of_eq_bot J hJ
  apply (HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := S) I).of_iso
    (asIso (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J)) (asIso (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I))
    (Iso.refl _) (Iso.refl _)
  · exact projectiveQuotientInclusion_coefficient I
  · change HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading J) ≫ 𝟙 _ =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion J ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading S n)
    dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient]
    rw [Category.comp_id]
    exact (projectiveQuotientInclusion_over J).symm
  · change HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) ≫ 𝟙 _ =
      HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)
    dsimp only [HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotient]
    rw [Category.comp_id]
    exact (projectiveQuotientInclusion_over I).symm
  · simp

/-- An actual isomorphism to the relative projective-space fiber product. -/
def polynomialProjectiveBaseChangeIso :
    Proj (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading S n) ≅ pullback (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) :=
  (polynomialProjective_isPullback (R := R) (S := S) (n := n)).isoPullback

end

end OAI.AlgebraicGeometry.Resolution.Blowups.PolynomialProjectiveBaseChange.Construction
