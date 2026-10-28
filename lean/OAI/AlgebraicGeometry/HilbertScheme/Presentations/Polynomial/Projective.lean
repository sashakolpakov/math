import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ChartPresentation
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.Properness

/-! # Projective -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective

noncomputable section

/-!
Standard affine covers and properness for projective polynomial quotients
with arbitrary finite coordinate index types.
-/

open _root_.MvPolynomial _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R σ : Type u} [CommRing R]

theorem quotient_irrelevant_le_span_variables (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) :
    (HomogeneousIdeal.irrelevant (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I)).toIdeal ≤
      Ideal.span (Set.range (fun i : σ => Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))) := by
  have h := Homogeneous.Quotient.HomogeneousQuotient.irrelevant_quotient_le_map I
  change (HomogeneousIdeal.irrelevant (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I)).toIdeal ≤
    Ideal.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (HomogeneousIdeal.irrelevant (Dehomogenization.PolynomialProjective.polynomialGrading σ R)).toIdeal at h
  apply h.trans
  have hr : (Set.range fun i : σ => Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i)) =
      Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I '' Set.range X := Set.range_comp' _ _
  rw [hr]
  erw [← Ideal.map_span]
  apply Ideal.map_mono
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (Dehomogenization.PolynomialProjective.polynomialGrading σ R)).mpr
  intro d hd f hf
  change f ∈ Ideal.span (Set.range (X : σ → MvPolynomial σ R))
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro a ha
  have had : a.degree = d := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      (show f.IsHomogeneous d from hf) (MvPolynomial.mem_support_iff.mp ha)
  have hex : ∃ i, a i ≠ 0 := by
    by_contra! hzero
    have haz : a = 0 := Finsupp.ext hzero
    rw [haz] at had
    simp only [map_zero] at had
    omega
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Set.mem_univ i, hi⟩

def projectiveQuotientAffineCover (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) :
    (Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotient I).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I)
    (fun i : σ => Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))
    (fun i => (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem (isHomogeneous_X R i))
    (fun _ => Nat.zero_lt_one) (quotient_irrelevant_le_span_variables I)

theorem quotientGrading_zero_algebraMap_surjective (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) :
    Function.Surjective (algebraMap R (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I 0)) := by
  intro q
  obtain ⟨f, hf, hq⟩ := q.property
  have hfeq : f = C (f.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous σ).mpr hf)
  refine ⟨f.coeff 0, Subtype.ext ?_⟩
  change Ideal.Quotient.mk I.toIdeal (C (f.coeff 0)) = q.val
  rw [← hfeq]
  exact hq

theorem projectiveQuotient_proper [Finite σ] (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) :
    IsProper (Projective.Flatness.GradedHilbert.projectiveStructureMap (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I)) :=
  Projective.Properness.GradedHilbert.projectiveStructureMap_proper (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I)
    (quotientGrading_zero_algebraMap_surjective I)

theorem dehomogenize_C_algebraMap (i : σ) (r : R) :
    Dehomogenization.PolynomialProjective.dehomogenize i (C r) = algebraMap R (HomogeneousLocalization.Away (Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X i)) r := by
  rw [Dehomogenization.PolynomialProjective.dehomogenize_C, Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  rfl

theorem quotientAwayMap_algebraMap (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) (i : σ) (r : R) :
    HomogeneousLocalization.Away.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (X i)
        (algebraMap R (HomogeneousLocalization.Away (Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X i)) r) =
      algebraMap R (HomogeneousLocalization.Away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))) r := by
  rw [← dehomogenize_C_algebraMap]
  exact ChartPresentation.PolynomialProjective.affineChartMap_C I i r

theorem projectiveQuotientInclusion_over (I : HomogeneousIdeal (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) :
    Homogeneous.ProjectiveQuotient.HomogeneousQuotient.projectiveQuotientInclusion I ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Dehomogenization.PolynomialProjective.polynomialGrading σ R) =
      Projective.Flatness.GradedHilbert.projectiveStructureMap (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) := by
  apply (projectiveQuotientAffineCover I).openCover.hom_ext
  intro i
  change σ at i
  have hi : X i ∈ Dehomogenization.PolynomialProjective.polynomialGrading σ R 1 := isHomogeneous_X R i
  change Proj.awayι (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))
    ((Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem hi) Nat.zero_lt_one ≫
      (Proj.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (Homogeneous.Quotient.HomogeneousQuotient.irrelevant_quotient_le_map I) ≫
        Projective.Flatness.GradedHilbert.projectiveStructureMap (Dehomogenization.PolynomialProjective.polynomialGrading σ R)) =
    Proj.awayι (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))
      ((Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem hi) Nat.zero_lt_one ≫
        Projective.Flatness.GradedHilbert.projectiveStructureMap (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I)
  rw [← Category.assoc, Proj.awayι_comp_map _ _ Nat.zero_lt_one (X i) hi, Category.assoc,
    Projective.Flatness.GradedHilbert.projectiveStructureMap_away (Dehomogenization.PolynomialProjective.polynomialGrading σ R) hi]
  refine Eq.trans ?_
    (Projective.Flatness.GradedHilbert.projectiveStructureMap_away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) ((Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I).map_mem hi)).symm
  rw [← Spec.map_comp]
  have hc : (HomogeneousLocalization.Away.map (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I) (X i)).comp
      (algebraMap R (HomogeneousLocalization.Away (Dehomogenization.PolynomialProjective.polynomialGrading σ R) (X i))) =
      algebraMap R (HomogeneousLocalization.Away (Homogeneous.Quotient.HomogeneousQuotient.quotientGrading I) (Homogeneous.Quotient.HomogeneousQuotient.gradedQuotientMap I (X i))) := by
    apply RingHom.ext
    exact quotientAwayMap_algebraMap I i
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hc

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.Projective.PolynomialProjective
