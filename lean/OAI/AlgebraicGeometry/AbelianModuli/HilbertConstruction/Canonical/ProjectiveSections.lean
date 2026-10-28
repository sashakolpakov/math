import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.CoordinateSectionRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PresentationSectionData

/-! # Projective Sections -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! A complete presentation has complete canonical coordinate sections
of its actual pulled-back projective twisting bundle. Completeness no
longer depends on the auxiliary sheaf used to supply the embedding. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
section
variable {S : Scheme.{u}} {X : Over S} (P : Projective.ProjectivePresentations.ProjectivePresentation X)

theorem Projective.ProjectivePresentations.ProjectivePresentation.canonicalSectionData_sections : P.canonicalSectionData.sections =
    fun i => Ample.LineBundles.pullbackSection P.embedding.left (Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S P.dimension i) := rfl

variable {P} {L : Line.Bundles.LineBundle X.left} (D : P.SectionData L)

theorem Projective.ProjectivePresentations.ProjectivePresentation.SectionData.twistingIso_coordinate (i : Fin (P.dimension + 1)) :
    Ample.LineBundles.pullbackSection P.embedding.left (Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S P.dimension i) ≫
      D.twistingIso.hom = D.sections i := by
  let h := congrArg Over.Hom.left D.embedding_eq
  let q := Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S P.dimension i
  let e := RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso X.hom D.sections D.covers
  change Ample.LineBundles.pullbackSection P.embedding.left q ≫
    ((Scheme.Modules.pullbackCongr h).hom.app _ ≫ e.hom) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.hom) (Global.SectionPullbackComposition.pullbackSection_equality h q)).trans
      (Relative.CoordinateSectionRecovery.sectionProjectiveTwistingBundleIso_coordinate X.hom D.sections D.covers i))

theorem Projective.ProjectivePresentations.ProjectivePresentation.SectionData.twistingIso_inverse_coordinate (i : Fin (P.dimension + 1)) :
    Ample.LineBundles.pullbackSection P.embedding.left (Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S P.dimension i) =
      D.sections i ≫ D.twistingIso.inv := by
  let s := Ample.LineBundles.pullbackSection P.embedding.left (Relative.CoordinateSectionRecovery.relativeProjectiveCoordinateSection S P.dimension i)
  have hc : (s ≫ D.twistingIso.hom) ≫ D.twistingIso.inv = s :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun k => s ≫ k) D.twistingIso.hom_inv_id).trans (Category.comp_id _))
  exact hc.symm.trans (congrArg (fun k => k ≫ D.twistingIso.inv) (D.twistingIso_coordinate i))

def Projective.ProjectivePresentations.ProjectivePresentation.SectionData.CompleteData.canonical (C : D.CompleteData) : P.canonicalSectionData.CompleteData := by
  let C' := C.ofBundleIso D.twistingIso.symm
  refine ⟨C'.basis, ?_⟩
  have hs : P.canonicalSectionData.sections = (D.ofBundleIso D.twistingIso.symm).sections := by
    funext i
    exact D.twistingIso_inverse_coordinate i
  exact hs.trans C'.sections_eq
end

variable {S : Scheme.{u}} {X : Over S} {L : Line.Bundles.LineBundle X.left}
variable (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) (D : E.CompleteSectionData)

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.CompleteSectionData.canonicalTwistingCompleteData : E.projectivePresentation.canonicalSectionData.CompleteData :=
  Projective.ProjectivePresentations.ProjectivePresentation.SectionData.CompleteData.canonical E.sectionData (D.presentationCompleteData E)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
