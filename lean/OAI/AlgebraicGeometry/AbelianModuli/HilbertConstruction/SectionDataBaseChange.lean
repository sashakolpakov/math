import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.BaseChangeIsoProjections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CanonicalGraph.Ampleness

/-! # Section Data Base Change -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionDataBaseChange

noncomputable section

/-! Section data follows the existing projective-presentation base change,
including its specific target isomorphism, over every changed base. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private theorem overPullback_map_return_eq {S T : Scheme.{u}} {X Y : Over S}
    {Z : Over T} (f : T ⟶ S) (e : Z ≅ (Over.pullback f).obj Y)
    (j : X ⟶ Y) (k : (Over.pullback f).obj X ⟶ Z) (p : Z.left ⟶ Y.left)
    (he : e.hom.left ≫ pullback.fst Y.hom f = p)
    (hk : pullback.fst X.hom f ≫ j.left = k.left ≫ p) :
    (Over.pullback f).map j ≫ e.inv = k := by
  apply (cancel_mono e.hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change ((Over.pullback f).map j).left ≫ pullback.fst Y.hom f =
      (k.left ≫ e.hom.left) ≫ pullback.fst Y.hom f
    rw [Pullback.Comparisons.overPullback_map_left_fst, Category.assoc, he]
    exact hk
  · exact ((Over.pullback f).map j).w.trans (k ≫ e.hom).w.symm

namespace ProjectivePresentation.SectionData
variable {S T : Scheme.{u}} {X : Over S} {P : Projective.ProjectivePresentations.ProjectivePresentation X} {L : Line.Bundles.LineBundle X.left}

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.SectionData.baseChange (D : P.SectionData L) (f : T ⟶ S) :
    (P.baseChange f).SectionData (L.pullback (pullback.fst X.hom f)) where
  sections i := Ample.LineBundles.pullbackSection (pullback.fst X.hom f) (D.sections i)
  covers := Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (pullback.fst X.hom f) L D.sections D.covers
  embedding_eq := by
    change (Over.pullback f).map P.embedding ≫
      (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f P.dimension).inv =
        SectionsProjectiveMorphism.sectionProjectiveMorphism (n := P.dimension) (pullback.snd X.hom f)
          (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom f) (D.sections i))
          (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (pullback.fst X.hom f) L D.sections D.covers)
    exact overPullback_map_return_eq f (Projective.SpaceBaseChange.projectiveSpaceOverBaseChangeIso f P.dimension)
      P.embedding
      (SectionsProjectiveMorphism.sectionProjectiveMorphism (pullback.snd X.hom f)
        (fun i => Ample.LineBundles.pullbackSection (pullback.fst X.hom f) (D.sections i))
        (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (pullback.fst X.hom f) L D.sections D.covers))
      (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f P.dimension)
      (Projective.BaseChangeIsoProjections.projectiveSpaceOverBaseChangeIso_hom_fst f P.dimension)
      ((congrArg (fun j => pullback.fst X.hom f ≫ j.left) D.embedding_eq).trans
        (Section.ProjectiveBaseChange.sectionProjectiveMorphism_baseChange (pullback.fst X.hom f) f X.hom
          (pullback.snd X.hom f) (IsPullback.of_hasPullback X.hom f).w L D.sections D.covers
          (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers (pullback.fst X.hom f) L D.sections D.covers)))

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation.SectionData.baseChangePowers {d : ℕ} (D : P.SectionData (L.tensorPower d)) (f : T ⟶ S) :
    (P.baseChange f).SectionData ((L.pullback (pullback.fst X.hom f)).tensorPower d) :=
  (D.baseChange f).ofBundleIso (L.powerBaseChangeIso (pullback.fst X.hom f) d)
end ProjectivePresentation.SectionData

namespace PolarizedAbelianWithFullLevel
variable {S T : Scheme.{u}} {g N : ℕ} {δ : Fin g → ℕ}
variable (A : PolarizationData.PolarizedAbelianWithFullLevel g δ N S)

def _root_.OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.PolarizationData.PolarizedAbelianWithFullLevel.graphEmbeddingBaseChangeSectionData
    (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding A.graphBundle A.abelian.scheme.hom) (f : T ⟶ S) :
    (E.projectivePresentation.baseChange f).SectionData ((A.pullback f).graphBundle.tensorPower E.degree) :=
  (E.canonicalPowerSectionData.baseChangePowers f).ofBundleIso
    ((TensorPower.Maps.tensorPowerFunctor (A.pullback f).abelian.scheme.left E.degree).mapIso
      (A.graphBundle_baseChangeIso f).symm)

end PolarizedAbelianWithFullLevel

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.SectionDataBaseChange
