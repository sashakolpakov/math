import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.EmbeddingProducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.ProjectiveTargetIso

/-! # Presentation Section Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Section data for a specified projective presentation is preserved by
native products and by an isomorphism of the defining line bundle. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

structure Projective.ProjectivePresentations.ProjectivePresentation.SectionData {S : Scheme.{u}} {X : Over S}
    (P : Projective.ProjectivePresentations.ProjectivePresentation X) (L : Line.Bundles.LineBundle X.left) where
  sections : Fin (P.dimension + 1) → (Line.Bundles.structureModule X.left ⟶ L.sheaf)
  covers : ∀ x : X.left, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (sections i)
  embedding_eq : P.embedding = Section.OverMaps.sectionProjectiveOverMap X (M := L.sheaf) sections covers

namespace Projective
variable {S : Scheme.{u}} {X Y : Over S} {P : ProjectivePresentations.ProjectivePresentation X} {Q : ProjectivePresentations.ProjectivePresentation Y}
variable {L L' : Line.Bundles.LineBundle X.left} {M : Line.Bundles.LineBundle Y.left}

def ProjectivePresentations.ProjectivePresentation.SectionData.twistingIso (D : P.SectionData L) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S P.dimension).pullback P.embedding.left).sheaf ≅ L.sheaf :=
  (Scheme.Modules.pullbackCongr (congrArg Over.Hom.left D.embedding_eq)).app
    (RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S P.dimension).sheaf ≪≫
      RelativeProjective.TwistingBundle.sectionProjectiveTwistingBundleIso X.hom D.sections D.covers

def ProjectivePresentations.ProjectivePresentation.SectionData.ofBundleIso (D : P.SectionData L) (e : L.sheaf ≅ L'.sheaf) : P.SectionData L' where
  sections i := D.sections i ≫ e.hom
  covers := Section.ProjectiveTargetIso.sections_compIso_covers e D.sections D.covers
  embedding_eq := D.embedding_eq.trans
    (Section.ProjectiveTargetIso.sectionProjectiveMorphism_targetIso X.hom e D.sections D.covers
      (Section.ProjectiveTargetIso.sections_compIso_covers e D.sections D.covers))

def ProjectivePresentations.ProjectivePresentation.SectionData.product (D : P.SectionData L) (E : Q.SectionData M) :
    (P.product Q).SectionData (Graph.ExternalTensorBundle.externalTensorBundle L M) where
  sections := Section.EmbeddingProducts.externalPairSectionFamily L M D.sections E.sections
  covers := Section.EmbeddingProducts.externalPairSectionFamily_covers L M D.sections E.sections D.covers E.covers
  embedding_eq := by
    change Products.projectiveProductEmbedding P.embedding Q.embedding = _
    rw [D.embedding_eq, E.embedding_eq]
    dsimp only [Graph.ExternalTensorBundle.externalTensorBundle, Section.EmbeddingProducts.externalPairSectionFamily]
    exact Section.EmbeddingProducts.tensorSectionProjectiveMorphism_segre L M D.sections E.sections D.covers E.covers

end Projective

variable {S : Scheme.{u}} {X : Over S} {L : Line.Bundles.LineBundle X.left}

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.projectivePresentation (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) : Projective.ProjectivePresentations.ProjectivePresentation X where
  dimension := E.dimension
  embedding := SectionsProjectiveMorphism.sectionProjectiveMorphism X.hom E.sections E.covers
  closedImmersion := E.closedImmersion

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.sectionData (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) : E.projectivePresentation.SectionData E.power where
  sections := E.sections
  covers := E.covers
  embedding_eq := rfl

def Power.ProjectiveEmbeddings.PowerProjectiveEmbedding.canonicalPowerSectionData (E : Power.ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) :
    E.projectivePresentation.SectionData (L.tensorPower E.degree) :=
  E.sectionData.ofBundleIso (E.isPower.unique (L.tensorPower_isTensorPower E.degree)).some

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
