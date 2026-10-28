import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.SectionLinearCoordinateAction
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.EmbeddingFrameCriterion
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.GeneratingSectionFrameChanges
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionData

/-! # Linear Coordinate Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Invertible coordinate changes preserve actual closed power
embeddings and their complete-section condition, with the ambient
projective automorphism explicitly identified. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X : Over S} {L : Line.Bundles.LineBundle X.left}
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom)
variable (e : (Fin (E.dimension + 1) →₀ Γ(S, ⊤)) ≃ₗ[Γ(S, ⊤)] (Fin (E.dimension + 1) →₀ Γ(S, ⊤)))

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.changeCoordinates : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom where
  degree := E.degree
  degree_pos := E.degree_pos
  power := E.power
  isPower := E.isPower
  dimension := E.dimension
  sections := Section.CoefficientTransformations.transformSectionFamily X.hom.appTop.hom E.power.sheaf E.sections e.symm.toLinearMap
  covers := GeneratingSectionFrameChanges.transformSectionFamily_covers X.hom.appTop.hom E.power E.sections E.covers
    e.symm.toLinearMap e.symm.surjective
  closedImmersion := by
    let a := Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso E.dimension S e
    let hs := GeneratingSectionFrameChanges.transformSectionFamily_covers X.hom.appTop.hom E.power E.sections E.covers
      e.symm.toLinearMap e.symm.surjective
    have hc : IsClosedImmersion (E.projectivePresentation.embedding ≫ a.hom).left :=
      @IsClosedImmersion.comp _ _ _ _ _ E.closedImmersion (Grassmann.ProjectivePresentation.overIso_closedImmersion a)
    exact (congrArg (fun m => IsClosedImmersion m.left)
      (Relative.SectionLinearCoordinateAction.sectionProjectiveMorphism_linearCoordinateIso X.hom E.sections E.covers e hs)).mp hc

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.changeCoordinates_embedding :
    (E.changeCoordinates e).projectivePresentation.embedding =
      E.projectivePresentation.embedding ≫ (Relative.LinearCoordinateIsomorphism.relativeLinearCoordinateIso E.dimension S e).hom :=
  (Relative.SectionLinearCoordinateAction.sectionProjectiveMorphism_linearCoordinateIso X.hom E.sections E.covers e _).symm

theorem Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.HasCompleteSections.changeCoordinates (h : E.HasCompleteSections) :
    (E.changeCoordinates e).HasCompleteSections := by
  apply ((E.changeCoordinates e).hasCompleteSections_iff_bijective).mpr
  exact GeneratingSectionFrameChanges.transformSectionFamily_complete X.hom.appTop.hom E.power E.sections
    (E.hasCompleteSections_iff_bijective.mp h) e.symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
