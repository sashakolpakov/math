import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationSectionData

/-! # Data Embedding Replacement -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

noncomputable section

/-! Replace a presentation embedding along a proved equality. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S : Scheme.{u}} {X : Over S} {P : Projective.ProjectivePresentations.ProjectivePresentation X} {L : Line.Bundles.LineBundle X.left}
def Projective.ProjectivePresentations.ProjectivePresentation.SectionData.withEmbedding (D : P.SectionData L)
    (j : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S P.dimension) (hj : IsClosedImmersion j.left)
    (he : P.embedding = j) :
    (⟨P.dimension, j, hj⟩ : Projective.ProjectivePresentations.ProjectivePresentation X).SectionData L where
  sections := D.sections
  covers := D.covers
  embedding_eq := he.symm.trans D.embedding_eq

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
