import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientBot
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.BaseChange

/-! # Projective Base Change -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveBaseChange.GradedHilbert

noncomputable section

/-! Polynomial projective space commutes with coefficient base change, and
the actual homogeneous quotient embeddings form cartesian squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {n : ℕ}

theorem extendedHomogeneousIdeal_bot :
    Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) = ⊥ := by
  apply HomogeneousIdeal.ext
  exact Ideal.map_bot

theorem polynomialProjective_isPullback :
    IsPullback (ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (algebraMap R S))
      (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading S n)) (Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n) := ⊥
  have hI : IsIso (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) := Projective.QuotientBot.GradedHilbert.projectiveQuotientBotInclusion_isIso R n
  have hJ : IsIso (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)) := by
    change IsIso (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S)
      (⊥ : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))))
    rw [extendedHomogeneousIdeal_bot]
    infer_instance
  let := hI
  let := hJ
  apply (Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := S) I).of_iso
    (asIso (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)))
    (asIso (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)) (Iso.refl _) (Iso.refl _)
  · exact ProjectiveCoefficientMap.GradedHilbert.projectiveCoefficientMap_inclusion I
  · exact (Category.comp_id _).trans
      (Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I)).symm
  · exact (Category.comp_id _).trans (Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure I).symm
  · simp

theorem polynomialProjectiveCoefficientMap_over :
    ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (algebraMap R S) ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) =
      Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading S n) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) :=
  polynomialProjective_isPullback.w

theorem projectiveQuotientCoefficientInclusion_isPullback (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    IsPullback (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I))
      (Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := S) I) (ProjectiveCoefficientMap.GradedHilbert.polynomialProjectiveCoefficientMap (n := n) (algebraMap R S))
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) := by
  have h : IsPullback (Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := S) I)
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion (Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := S) I) ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading S n))
      (Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ Projective.Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
    rw [Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure, Projective.QuotientStructure.GradedHilbert.projectiveQuotientInclusion_structure]
    exact Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback I
  exact (h.of_bot (ProjectiveCoefficientMap.GradedHilbert.projectiveCoefficientMap_inclusion I)
    (polynomialProjective_isPullback (R := R) (S := S) (n := n))).flip

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Polynomial.ProjectiveBaseChange.GradedHilbert
