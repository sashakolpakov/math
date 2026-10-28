import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.IdealBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Homogeneous.ProjectiveFamilies
import OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial

/-! # Saturation Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SaturationBaseChange

noncomputable section

/-! Projective saturation commutes with coefficient extension after saturation, and preserves the actual flat family and field Hilbert polynomial. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

theorem projectiveSaturation_baseChange (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation I)) =
      HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) := by
  apply congrArg HilbertScheme.Presentations.ChartHomogeneousIdeal.GradedHilbert.homogeneousIdealOfSheaf
  rw [IdealBaseChange.projectiveQuotientIdeal_baseChange, IdealBaseChange.projectiveQuotientIdeal_baseChange,
    HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf]

omit [Algebra R A] in
def homogeneousProjectiveSaturationIso (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation I) ≅ EmbeddingBaseChange.homogeneousProjectiveFamily I :=
  Homogeneous.ProjectiveFamilies.homogeneousProjectiveFamilyIso (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation I) I (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation_idealSheaf I)

omit [Algebra R A] in
theorem projectiveSaturation_flat (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    [Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))] :
    Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation I))) := by
  let e := homogeneousProjectiveSaturationIso I
  have : IsIso e.hom.left := (Over.forget _).map_isIso e.hom
  have : Flat (EmbeddingBaseChange.homogeneousProjectiveFamily I).hom :=
    inferInstanceAs (Flat (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)))
  have hh : Flat (e.hom.left ≫ (EmbeddingBaseChange.homogeneousProjectiveFamily I).hom) := inferInstance
  change Flat (EmbeddingBaseChange.homogeneousProjectiveFamily (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation I)).hom
  exact e.hom.w ▸ hh

omit [Algebra R A] in
theorem projectiveSaturation_fieldHilbertPolynomial (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))
    (K : Type u) [Field K] [Algebra R K] (P : Polynomial ℚ) :
    HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial
      (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) (HilbertScheme.Presentations.Projective.Saturation.GradedHilbert.projectiveSaturation I))).toIdeal P ↔
        HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.HasHilbertPolynomial (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := K) I).toIdeal P := by
  rw [projectiveSaturation_baseChange, HilbertScheme.Presentations.Saturation.Polynomial.GradedHilbert.projectiveSaturation_hasHilbertPolynomial_iff]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SaturationBaseChange
