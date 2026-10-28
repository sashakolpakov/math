import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Flat.ProjectiveCoordinatePieces

/-! # Quotient Structure -/

namespace OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientStructure.GradedHilbert

noncomputable section

/-! The projective quotient inclusion and the structure morphism commute over the coefficient ring. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.HomogeneousLocalization _root_.MvPolynomial

universe u

variable {R : Type u} [CommRing R] {n : ℕ}

theorem quotientChartMap_algebraMap (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n))
    (s : Hilbert.Polynomial.GradedHilbert.CoordinateRing R n) (r : R) :
    HomogeneousLocalization.Away.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) s
      (algebraMap R (HomogeneousLocalization.Away (Hilbert.Polynomial.GradedHilbert.grading R n) s) r) =
      algebraMap R (HomogeneousLocalization.Away (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I s)) r := by
  rw [Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap, Homogeneous.LocalizationFlat.GradedHilbert.homogeneousLocalization_algebraMap]
  apply HomogeneousLocalization.val_injective
  change Localization.mk (Graded.Quotient.GradedHilbert.gradedQuotientMap I ((algebraMap R (Hilbert.Polynomial.GradedHilbert.grading R n 0) r).val))
    ⟨Graded.Quotient.GradedHilbert.gradedQuotientMap I 1, _⟩ =
      Localization.mk ((algebraMap R (Graded.Quotient.GradedHilbert.quotientGrading I 0) r).val) 1
  congr 1

theorem projectiveQuotientInclusion_structure (I : HomogeneousIdeal (Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ Flatness.GradedHilbert.projectiveStructureMap (Hilbert.Polynomial.GradedHilbert.grading R n) =
      Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I) := by
  let U := Proj.affineOpenCoverOfIrrelevantLESpan (Graded.Quotient.GradedHilbert.quotientGrading I)
    (fun i : Fin (n + 1) => Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
    (fun i => (Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i))
    (fun _ => Nat.zero_lt_one) (Flatness.GradedHilbert.quotient_irrelevant_le_span_variables I)
  apply U.openCover.hom_ext
  intro i
  change Fin (n + 1) at i
  change Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
      ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i)) Nat.zero_lt_one ≫
      (Proj.map (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I) ≫ _) =
    Proj.awayι (Graded.Quotient.GradedHilbert.quotientGrading I) (Graded.Quotient.GradedHilbert.gradedQuotientMap I (X i))
      ((Graded.Quotient.GradedHilbert.gradedQuotientMap I).map_mem (isHomogeneous_X R i)) Nat.zero_lt_one ≫
      Flatness.GradedHilbert.projectiveStructureMap (Graded.Quotient.GradedHilbert.quotientGrading I)
  rw [Proj.awayι_comp_map_assoc (Graded.Quotient.GradedHilbert.gradedQuotientMap I) (Graded.Quotient.GradedHilbert.irrelevant_quotient_le_map I)
    Nat.zero_lt_one (X i) (isHomogeneous_X R i)]
  erw [Flatness.GradedHilbert.projectiveStructureMap_away (Hilbert.Polynomial.GradedHilbert.grading R n) (isHomogeneous_X R i)]
  rw [Flatness.GradedHilbert.projectiveStructureMap_away, ← Spec.map_comp]
  congr 1

end

end OAI.AlgebraicGeometry.HilbertScheme.Presentations.Projective.QuotientStructure.GradedHilbert
