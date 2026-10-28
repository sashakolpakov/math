import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.QuotientCoordinateChart
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.MorphismOpenFrame
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpecIsoProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.EmbeddingBaseChange

/-! # Quotient Section Morphism -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.QuotientSectionMorphism

noncomputable section

/-! The morphism defined by the actual homogeneous coordinate sections
is precisely the existing projective quotient embedding, including the
native comparison over the spectrum of the coefficient ring. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type u} [CommRing R] {n : ℕ} (I : HomogeneousIdeal (HilbertScheme.Presentations.Hilbert.Polynomial.GradedHilbert.grading R n))

theorem sectionAbsoluteMorphism_projectiveCoordinates :
    SectionsProjectiveMorphism.sectionAbsoluteMorphism (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
      (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I) (ProjectiveCoordinate.SectionFrames.projectiveCoordinateSectionFamily_covers I) =
    HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso (.of R)).hom n := by
  let p := HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I)
  let s := ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I
  let hs := ProjectiveCoordinate.SectionFrames.projectiveCoordinateSectionFamily_covers I
  apply (SectionsProjectiveMorphism.sectionOpenCover s hs).hom_ext
  intro i
  change Fin (n + 1) at i
  change (Ample.LineBundles.sectionNonvanishing (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I i)).ι ≫ _ =
    (Ample.LineBundles.sectionNonvanishing (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I i)).ι ≫ _
  erw [ProjectiveCoordinate.Nonvanishing.projectiveCoordinateSection_nonvanishing]
  let U := ProjectiveChart.SectionCoordinates.coordinateProjectiveChartOpen I {i}
  let c := QuotientCoordinateChart.coordinateSectionChartCoefficients I i
  let v := QuotientCoordinateChart.coordinateSectionChartValues I i
  let hv := QuotientCoordinateChart.coordinateSectionChartValues_pivot I i
  have hc : c.comp (Scheme.ΓSpecIso (.of R)).hom.hom = (U.ι ≫ p).appTop.hom := by
    dsimp only [c]
    rw [QuotientCoordinateChart.coordinateSectionChartCoefficients_structural]
    exact ProjectiveChart.CoefficientRecovery.schemeCoefficientMap_comp_specGlobalIso (U.ι ≫ p)
  calc
    U.ι ≫ SectionsProjectiveMorphism.sectionAbsoluteMorphism p s hs =
        ProjectiveChart.Evaluation.projectiveChartMap (U.ι ≫ p).appTop.hom
          (fun j => Frame.Coordinates.frameCoordinate (Ample.LineBundles.pullbackSection U.ι (s i)) (Ample.LineBundles.pullbackSection U.ι (s j))) i
          (Frame.Coordinates.frameCoordinate_self (Ample.LineBundles.pullbackSection U.ι (s i))) :=
      Section.MorphismOpenFrame.sectionAbsoluteMorphism_on_open_frame p s hs U i
    _ = ProjectiveChart.Evaluation.projectiveChartMap (c.comp (Scheme.ΓSpecIso (.of R)).hom.hom) v i hv :=
      Framed.ProjectiveMaps.projectiveChartMap_congr_coefficients hc.symm
        (funext fun j => ProjectiveCoordinate.SectionFrames.projectiveCoordinateSection_frameCoordinate I i j) i _ _
    _ = ProjectiveChart.Evaluation.projectiveChartMap c v i hv ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso (.of R)).hom n :=
      (ProjectiveChart.CoefficientNaturality.projectiveChartMap_coefficientMap (Scheme.ΓSpecIso (.of R)).hom.hom c v i hv).symm
    _ = U.ι ≫ (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso (.of R)).hom n) := by
      rw [← QuotientCoordinateChart.projectiveQuotientInclusion_coordinateChart, Category.assoc]

theorem sectionProjectiveMorphism_projectiveCoordinates :
    SectionsProjectiveMorphism.sectionProjectiveMorphism (HilbertScheme.Presentations.Projective.Flatness.GradedHilbert.projectiveStructureMap (HilbertScheme.Presentations.Graded.Quotient.GradedHilbert.quotientGrading I))
      (ProjectiveCoordinate.GlobalSections.projectiveCoordinateSection I) (ProjectiveCoordinate.SectionFrames.projectiveCoordinateSectionFamily_covers I) =
    Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I ≫ (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv := by
  apply Over.OverMorphism.ext
  apply (RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection_isPullback (Spec (.of R)) n).hom_ext
  · rw [Section.ProjectiveBaseChange.sectionProjectiveMorphism_coefficientProjection, sectionAbsoluteMorphism_projectiveCoordinates]
    change HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ Projective.CoefficientFunctoriality.polynomialProjectiveMap (Scheme.ΓSpecIso (.of R)).hom n =
      (HilbertScheme.Presentations.Projective.Quotient.GradedHilbert.projectiveQuotientInclusion I ≫ (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv.left) ≫
        RelativeProjective.BaseMaps.relativeProjectiveCoefficientProjection (Spec (.of R)) n
    erw [Category.assoc, Projective.SpecIsoProjections.projectiveSpaceOverSpecIso_inv_coefficients]
  · exact (SectionsProjectiveMorphism.sectionProjectiveMorphism _ _ _).w.trans
      (Projective.EmbeddingBaseChange.homogeneousProjectiveEmbedding I ≫ (Projective.SpaceBaseChange.projectiveSpaceOverSpecIso (.of R) n).inv).w.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Canonical.QuotientSectionMorphism
