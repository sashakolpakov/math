import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.EmbeddingIntrinsic

/-! # Presentation Section Data -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Restrict section data along a closed immersion and retain it for the
native product presentation of a morphism graph. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u

def Projective.ProjectivePresentations.ProjectivePresentation.precomp {S : Scheme.{u}} {X Y : Over S}
    (P : Projective.ProjectivePresentations.ProjectivePresentation Y) (a : X ⟶ Y) [IsClosedImmersion a.left] : Projective.ProjectivePresentations.ProjectivePresentation X where
  dimension := P.dimension
  embedding := a ≫ P.embedding
  closedImmersion := @IsClosedImmersion.comp _ _ _ _ _ inferInstance P.closedImmersion

def Projective.ProjectivePresentations.ProjectivePresentation.SectionData.precomp {S : Scheme.{u}} {X Y : Over S}
    {P : Projective.ProjectivePresentations.ProjectivePresentation Y} {L : Line.Bundles.LineBundle Y.left}
    (D : P.SectionData L) (a : X ⟶ Y) [IsClosedImmersion a.left] :
    (P.precomp a).SectionData (L.pullback a.left) where
  sections i := Ample.LineBundles.pullbackSection a.left (D.sections i)
  covers := Section.ChartArbitraryPullback.lineBundleSections_pullback_covers a.left L D.sections D.covers
  embedding_eq := (congrArg (fun j => a ≫ j) D.embedding_eq).trans
    (Section.ProjectivePrecomposition.sectionProjectiveMorphism_precomp a L D.sections D.covers
      (Section.ChartArbitraryPullback.lineBundleSections_pullback_covers a.left L D.sections D.covers))

variable {S : Scheme.{u}} {X Y : Over S} (P : Projective.ProjectivePresentations.ProjectivePresentation X) (Q : Projective.ProjectivePresentations.ProjectivePresentation Y)
variable [IsSeparated Y.hom]

def Projective.ProjectivePresentations.ProjectivePresentation.graph (p : X ⟶ Y) : Projective.ProjectivePresentations.ProjectivePresentation X :=
  (P.product Q).precomp (MorphismGraphFamilies.familyGraph p)

variable {P Q} {L : Line.Bundles.LineBundle X.left} {M : Line.Bundles.LineBundle Y.left}

def Projective.ProjectivePresentations.ProjectivePresentation.SectionData.graph
    (D : P.SectionData L) (E : Q.SectionData M) (p : X ⟶ Y) :
    (P.graph Q p).SectionData (L.tensor (M.pullback p.left)) :=
  ((D.product E).precomp (MorphismGraphFamilies.familyGraph p)).ofBundleIso (Graph.ExternalTensorBundle.graphExternalTensorBundleIso p L M)

def Projective.ProjectivePresentations.ProjectivePresentation.SectionData.graphTwistingIso
    (D : P.SectionData L) (E : Q.SectionData M) (p : X ⟶ Y) :
    ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle S (P.product Q).dimension).pullback
      (MorphismGraphFamilies.familyGraph p ≫ (P.product Q).embedding).left).sheaf ≅ (L.tensor (M.pullback p.left)).sheaf :=
  (D.graph E p).twistingIso

variable {K : Type u} [Field K] {A B : Over (Spec (.of K))}
variable [Flat A.hom] [LocallyOfFinitePresentation A.hom] [IsSeparated B.hom]
variable {PA : Projective.ProjectivePresentations.ProjectivePresentation A} {PB : Projective.ProjectivePresentations.ProjectivePresentation B}
variable {LA : Line.Bundles.LineBundle A.left} {LB : Line.Bundles.LineBundle B.left}

theorem Projective.ProjectivePresentations.ProjectivePresentation.SectionData.graphHilbertPolynomial_iff
    (D : PA.SectionData LA) (E : PB.SectionData LB) (p : A ⟶ B) (P : Polynomial ℚ) :
    Embedded.GraphHilbertBaseChange.HasEmbeddedGraphHilbertPolynomial (PA.product PB).embedding P p ↔
      (LA.tensor (LB.pullback p.left)).HasSectionHilbertPolynomial A.hom P :=
  (Relative.EmbeddingIntrinsic.embeddedGraph_intrinsicHilbertPolynomial_iff (PA.product PB).embedding P p).trans
    (Line.Bundles.LineBundle.hasSectionHilbertPolynomial_iff_of_sheafIso A.hom
      ((RelativeProjective.TwistingBundle.relativeProjectiveTwistingBundle (Spec (.of K)) (PA.product PB).dimension).pullback
        (MorphismGraphFamilies.familyGraph p ≫ (PA.product PB).embedding).left)
      (LA.tensor (LB.pullback p.left)) (D.graphTwistingIso E p) P)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
