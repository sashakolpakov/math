import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Polynomial.ProjectiveCoefficients

/-! # Coefficient Pullback -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientPullback

noncomputable section

/-!
Coefficient changes give Cartesian squares for standard projective spaces
and their actual homogeneous closed subschemes, including the embeddings.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

theorem projectiveQuotientInclusion_standard_over (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ (ProjectivePresentations.affineProjectiveSpace R n).hom =
      HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) := by
  change Proj.map (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) _ ≫
    (Proj.toSpecZero (ProjectivePresentations.coordinateGrading R n) ≫
      Spec.map (CommRingCat.ofHom (ProjectivePresentations.degreeZeroConstants R n).toRingHom)) = _
  rw [SpaceReindex.degreeZeroConstants_eq_algebraMap]
  exact MapOverBase.projectiveMap_over_base _ _ (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.gradedQuotientMap I) _ (fun _ => rfl)

theorem projectiveQuotientInclusion_zero_isIso (R : Type u) [CommRing R] (n : ℕ) :
    IsIso (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))) := by
  change IsIso (QuotientZero.projectiveQuotientZeroIso R n).hom.left
  exact (Over.forget (Spec (CommRingCat.of R))).map_isIso (QuotientZero.projectiveQuotientZeroIso R n).hom

theorem polynomialProjectiveCoefficient_isPullback :
    IsPullback (Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap (R := R) (A := A) (n := n))
      (ProjectivePresentations.affineProjectiveSpace A n).hom (ProjectivePresentations.affineProjectiveSpace R n).hom
        (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
  let I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n) := ⊥
  have : IsIso (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) := projectiveQuotientInclusion_zero_isIso R n
  have : IsIso (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)) := by
    change IsIso (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A)
      (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))))
    rw [QuotientZero.extendedHomogeneousIdeal_zero]
    exact projectiveQuotientInclusion_zero_isIso A n
  let eR := asIso (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)
  let eA := asIso (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))
  apply (HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := A) I).of_iso eA eR (Iso.refl _) (Iso.refl _)
  · exact (Polynomial.ProjectiveCoefficients.projectiveQuotientInclusion_coefficient (A := A) I).symm
  · change HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (projectiveQuotientInclusion_standard_over (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)).symm
  · change HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I) ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (projectiveQuotientInclusion_standard_over I).symm
  · simp

theorem projectiveQuotientEmbedding_isPullback (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    IsPullback (HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := A) I)
      (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I))
      (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) (Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap (R := R) (A := A)) := by
  have h : IsPullback (HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := A) I)
      (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) ≫ (ProjectivePresentations.affineProjectiveSpace A n).hom)
      (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ (ProjectivePresentations.affineProjectiveSpace R n).hom)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    rw [projectiveQuotientInclusion_standard_over, projectiveQuotientInclusion_standard_over]
    exact HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback I
  exact h.of_bot (Polynomial.ProjectiveCoefficients.projectiveQuotientInclusion_coefficient I).symm
    polynomialProjectiveCoefficient_isPullback

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.CoefficientPullback
