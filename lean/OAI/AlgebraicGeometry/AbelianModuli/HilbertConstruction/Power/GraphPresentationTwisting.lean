import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.PresentationSectionData
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Parallelogram
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationAmpleBundle

/-! # Graph Presentation Twisting -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Native product and graph presentations of power embeddings retain the
same tensor degree. Their twisting bundles are the corresponding powers
of the external or graph line bundles. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {X Y : Over S}

def Power.GraphPresentationTwisting.externalTensorBundle_tensorPowerIso (L : Line.Bundles.LineBundle X.left) (M : Line.Bundles.LineBundle Y.left) (d : ℕ) :
    (Graph.ExternalTensorBundle.externalTensorBundle (L.tensorPower d) (M.tensorPower d)).sheaf ≅
      ((Graph.ExternalTensorBundle.externalTensorBundle L M).tensorPower d).sheaf :=
  Tensor.Bifunctor.tensorModuleMapIso (L.powerBaseChangeIso (fst X Y).left d)
    (M.powerBaseChangeIso (snd X Y).left d) ≪≫
      ((L.pullback (fst X Y).left).tensorPowerTensorIso (M.pullback (snd X Y).left) d).symm

def Power.GraphPresentationTwisting.graphTensorPowerIso (p : X ⟶ Y) (L : Line.Bundles.LineBundle X.left) (M : Line.Bundles.LineBundle Y.left) (d : ℕ) :
    ((L.tensorPower d).tensor ((M.tensorPower d).pullback p.left)).sheaf ≅
      ((L.tensor (M.pullback p.left)).tensorPower d).sheaf :=
  Tensor.Bifunctor.tensorModuleMapIso (Iso.refl _) (M.powerBaseChangeIso p.left d) ≪≫
    (L.tensorPowerTensorIso (M.pullback p.left) d).symm

section
variable {P : Projective.ProjectivePresentations.ProjectivePresentation X} {Q : Projective.ProjectivePresentations.ProjectivePresentation Y}
variable {L : Line.Bundles.LineBundle X.left} {M : Line.Bundles.LineBundle Y.left} {d : ℕ}

def Projective.ProjectivePresentations.ProjectivePresentation.SectionData.productPowers (D : P.SectionData (L.tensorPower d)) (E : Q.SectionData (M.tensorPower d)) :
    (P.product Q).SectionData ((Graph.ExternalTensorBundle.externalTensorBundle L M).tensorPower d) :=
  (D.product E).ofBundleIso (Power.GraphPresentationTwisting.externalTensorBundle_tensorPowerIso L M d)

def Projective.ProjectivePresentations.ProjectivePresentation.SectionData.graphPowers [IsSeparated Y.hom]
    (D : P.SectionData (L.tensorPower d)) (E : Q.SectionData (M.tensorPower d)) (p : X ⟶ Y) :
    (P.graph Q p).SectionData ((L.tensor (M.pullback p.left)).tensorPower d) :=
  (D.graph E p).ofBundleIso (Power.GraphPresentationTwisting.graphTensorPowerIso p L M d)

theorem Projective.ProjectivePresentations.ProjectivePresentation.SectionData.isAmple [IsAffine S] (D : P.SectionData L) : L.IsAmple :=
  P.ampleLineBundle_isAmple.of_iso D.twistingIso
end

namespace Power
variable {L : Line.Bundles.LineBundle X.left} [IsSeparated X.hom]

def ProjectiveEmbeddings.PowerProjectiveEmbedding.binaryGraphSectionData (E : ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) (p : X ⊗ X ⟶ X) :
    ((E.projectivePresentation.product E.projectivePresentation).graph E.projectivePresentation p).SectionData (((Graph.ExternalTensorBundle.externalTensorBundle L L).tensor (L.pullback p.left)).tensorPower E.degree) :=
  (E.canonicalPowerSectionData.productPowers E.canonicalPowerSectionData).graphPowers E.canonicalPowerSectionData p

def ProjectiveEmbeddings.PowerProjectiveEmbedding.unaryGraphSectionData (E : ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) (p : X ⟶ X) :
    (E.projectivePresentation.graph E.projectivePresentation p).SectionData ((L.tensor (L.pullback p.left)).tensorPower E.degree) :=
  E.canonicalPowerSectionData.graphPowers E.canonicalPowerSectionData p

theorem ProjectiveEmbeddings.PowerProjectiveEmbedding.binaryGraphBundle_isAmple [IsAffine S]
    (E : ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) (p : X ⊗ X ⟶ X) :
    ((Graph.ExternalTensorBundle.externalTensorBundle L L).tensor (L.pullback p.left)).IsAmple :=
  Line.Bundles.LineBundle.IsAmple.of_tensorPower E.degree E.degree_pos (E.binaryGraphSectionData p).isAmple

theorem ProjectiveEmbeddings.PowerProjectiveEmbedding.unaryGraphBundle_isAmple [IsAffine S]
    (E : ProjectiveEmbeddings.PowerProjectiveEmbedding L X.hom) (p : X ⟶ X) :
    (L.tensor (L.pullback p.left)).IsAmple :=
  Line.Bundles.LineBundle.IsAmple.of_tensorPower E.degree E.degree_pos (E.unaryGraphSectionData p).isAmple
end Power

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
