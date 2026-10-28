import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Embedding Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingBaseChange

noncomputable section

/-!
Base-change isomorphisms for homogeneous projective families preserve their
actual closed embeddings into standard projective space.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] {n : ℕ}

def homogeneousProjectiveFamily (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) : Over (Spec (CommRingCat.of R)) :=
  Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))

def homogeneousProjectiveEmbedding (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    homogeneousProjectiveFamily I ⟶ ProjectivePresentations.affineProjectiveSpace R n :=
  Over.homMk (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I) (CoefficientPullback.projectiveQuotientInclusion_standard_over I)

def homogeneousProjectiveBaseChangeIso (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    homogeneousProjectiveFamily (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj (homogeneousProjectiveFamily I) :=
  Over.isoMk (HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotientBaseChangeIso (S := A) I)
    ((HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := A) I).isoPullback_hom_snd)

theorem homogeneousProjectiveEmbedding_baseChange (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (homogeneousProjectiveBaseChangeIso (A := A) I).hom ≫
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map (homogeneousProjectiveEmbedding I) =
        homogeneousProjectiveEmbedding (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I) ≫
          (SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := R) (A := A) n).hom := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap R A))
  let j := homogeneousProjectiveEmbedding I
  let j' := homogeneousProjectiveEmbedding (HilbertScheme.Presentations.Graded.BaseChange.GradedHilbert.extendedHomogeneousIdeal (S := A) I)
  let e := homogeneousProjectiveBaseChangeIso (A := A) I
  let eP := SpaceBaseChange.affineProjectiveSpaceBaseChangeIso (R := R) (A := A) n
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · have hc := (PresentationBaseChange.overPullback_map_isPullback j f).w
    have he : e.hom.left ≫ pullback.fst (homogeneousProjectiveFamily I).hom f =
        HilbertScheme.Presentations.Projective.CoefficientMap.GradedHilbert.projectiveCoefficientMap (S := A) I :=
      (HilbertScheme.Presentations.Projective.BaseChange.GradedHilbert.projectiveQuotient_isPullback (S := A) I).isoPullback_hom_fst
    have hP : eP.hom.left ≫ pullback.fst (ProjectivePresentations.affineProjectiveSpace R n).hom f =
        Polynomial.ProjectiveCoefficients.polynomialProjectiveCoefficientMap (R := R) (A := A) (n := n) :=
      SpaceBaseChange.affineProjectiveSpaceBaseChangeIso_hom_fst n
    change (e.hom.left ≫ ((Over.pullback f).map j).left) ≫
      pullback.fst (ProjectivePresentations.affineProjectiveSpace R n).hom f =
        (j'.left ≫ eP.hom.left) ≫ pullback.fst (ProjectivePresentations.affineProjectiveSpace R n).hom f
    rw [Category.assoc, ← hc, ← Category.assoc, he, Category.assoc, hP]
    exact (Polynomial.ProjectiveCoefficients.projectiveQuotientInclusion_coefficient I).symm
  · exact (e.hom ≫ (Over.pullback f).map j).w.trans (j' ≫ eP.hom).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingBaseChange
