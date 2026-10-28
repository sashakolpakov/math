import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.QuotientSectionMorphism
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionDataBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.PresentationSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationAmpleBundle

/-! # Coordinate Section Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateSectionData

noncomputable section

/-! Every existing projective presentation has canonical section data for
its pulled-back O(1). The construction follows the quotient coordinates,
the affine standard space, and then the native arbitrary-base comparison. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type u} [CommRing R] {n : ℕ}

def quotientCoordinatePresentation (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    Projective.ProjectivePresentations.ProjectivePresentation (Projective.EmbeddingBaseChange.homogeneousProjectiveFamily I) where
  dimension := n
  embedding := Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I ≫ (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv
  closedImmersion := @IsClosedImmersion.comp _ _ _ _ _
    (inferInstanceAs (IsClosedImmersion (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I)))
    (Grassmann.ProjectivePresentation.overIso_closedImmersion (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).symm)

def quotientCoordinateSectionData (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) :
    (quotientCoordinatePresentation I).SectionData (ProjectiveTwisting.Bundle.projectiveTwistingBundle I 1) where
  sections := ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I
  covers := ProjectiveCoordinate.SectionFrames.projectiveCoordinateSectionFamily_covers I
  embedding_eq := (Canonical.QuotientSectionMorphism.sectionProjectiveMorphism_projectiveCoordinates I).symm

private def presentationOfEmbedding {S : Scheme.{u}} {Y : Over S} {n : ℕ}
    (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (hj : IsClosedImmersion j.left) : Projective.ProjectivePresentations.ProjectivePresentation Y where
  dimension := n
  embedding := j
  closedImmersion := hj

private def affineSpecInv (R : Type u) [CommRing R] (n : ℕ) :
    Projective.ProjectivePresentations.affineProjectiveSpace R n ⟶ Projective.ProjectivePresentations.projectiveSpaceOver (Spec (CommRingCat.of R)) n :=
  (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (CommRingCat.of R) n).inv

private theorem affineSpecInv_closed (R : Type u) [CommRing R] (n : ℕ) :
    IsClosedImmersion (affineSpecInv R n).left :=
  Grassmann.ProjectivePresentation.overIso_closedImmersion (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (CommRingCat.of R) n).symm

abbrev affineCoordinatePresentation (R : Type u) [CommRing R] (n : ℕ) :
    Projective.ProjectivePresentations.ProjectivePresentation (Projective.ProjectivePresentations.affineProjectiveSpace R n) :=
  Projective.PresentationBaseChange.nativeAffineProjectivePresentation (CommRingCat.of R) n

private def sectionDataFromIso {S : Scheme.{u}} {X Y : Over S} {n : ℕ}
    (e : X ≅ Y) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (hj : IsClosedImmersion j.left)
    (L : Line.Bundles.LineBundle X.left)
    (s : Fin (n + 1) → (Line.Bundles.structureModule X.left ⟶ L.sheaf))
    (hs : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i))
    (he : SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom s hs = e.hom ≫ j) :
    (presentationOfEmbedding j hj).SectionData (L.pullback e.inv.left) where
  sections i := Ample.LineBundles.pullbackSection e.inv.left (s i)
  covers := Section.ChartArbitraryPullback.lineBundleSections_pullback_covers e.inv.left L s hs
  embedding_eq := (Iso.inv_hom_id_assoc e j).symm.trans
    ((congrArg (fun k => e.inv ≫ k) he.symm).trans
      (Section.ProjectivePrecomposition.sectionProjectiveMorphism_precomp e.inv L s hs
        (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers e.inv.left L s hs)))

private theorem isoInvClosed {S : Scheme.{u}} {X Y : Over S} (e : X ≅ Y) :
    IsClosedImmersion e.inv.left := Grassmann.ProjectivePresentation.overIso_closedImmersion e.symm

private abbrev affineCoordinateClosed (R : Type u) [CommRing R] (n : ℕ) :=
  isoInvClosed (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n)

private abbrev affineCoordinateCovers (R : Type u) [CommRing R] (n : ℕ) :=
  ProjectiveCoordinate.SectionFrames.projectiveCoordinateSectionFamily_covers (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

private theorem quotientZeroIso_hom (R : Type u) [CommRing R] (n : ℕ) :
    (Projective.QuotientZero.projectiveQuotientZeroIso R n).hom =
      Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) := by
  apply Over.OverMorphism.ext
  rfl

private theorem affineSpecInv_left (R : Type u) [CommRing R] (n : ℕ) :
    (affineSpecInv R n).left = (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (CommRingCat.of R) n).inv.left := rfl

private theorem affineCoordinateMap (R : Type u) [CommRing R] (n : ℕ) :
    SectionsProjectiveMorphism.sectionProjectiveMorphism
      (Over.mk (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))))).hom
      (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)))
      (ProjectiveCoordinate.SectionFrames.projectiveCoordinateSectionFamily_covers (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))) =
      (Projective.QuotientZero.projectiveQuotientZeroIso R n).hom ≫ affineSpecInv R n := by
  apply Over.OverMorphism.ext
  have h := congrArg Over.Hom.left
    (Canonical.QuotientSectionMorphism.sectionProjectiveMorphism_projectiveCoordinates (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)))
  change (SectionsProjectiveMorphism.sectionProjectiveMorphism _ _ _).left =
    (Projective.QuotientZero.projectiveQuotientZeroIso R n).hom.left ≫ (affineSpecInv R n).left
  rw [affineSpecInv_left, quotientZeroIso_hom]
  exact h

def affineCoordinateSectionData (R : Type u) [CommRing R] (n : ℕ) :
    (affineCoordinatePresentation R n).SectionData (Section.AbsoluteTwistingBundle.affineProjectiveTwistingBundle R n) where
  sections i := Ample.LineBundles.pullbackSection (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left
    (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) i)
  covers := Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left
    (ProjectiveTwisting.Bundle.projectiveTwistingBundle (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) 1)
    (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)))
    (affineCoordinateCovers R n)
  embedding_eq :=
    (Iso.inv_hom_id_assoc (Projective.QuotientZero.projectiveQuotientZeroIso R n) (affineSpecInv R n)).symm.trans
      ((congrArg (fun k => (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv ≫ k)
        (affineCoordinateMap R n).symm).trans
          (Section.ProjectivePrecomposition.sectionProjectiveMorphism_precomp (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv
            (ProjectiveTwisting.Bundle.projectiveTwistingBundle (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) 1)
            (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)))
            (affineCoordinateCovers R n)
            (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (Projective.QuotientZero.projectiveQuotientZeroIso R n).inv.left
              (ProjectiveTwisting.Bundle.projectiveTwistingBundle (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)) 1)
              (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection (⊥ : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n)))
              (affineCoordinateCovers R n))))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CoordinateSectionData
