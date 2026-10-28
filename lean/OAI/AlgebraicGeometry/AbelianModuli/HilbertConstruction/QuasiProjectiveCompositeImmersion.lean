import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.SpaceOverComposition
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveProducts

/-! # Quasi Projective Composite Immersion -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveCompositeImmersion

noncomputable section

/-! A composition of quasi-projective presentations has a specified immersion into the projective product of the outer compactification and a projective space. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S : Scheme.{u}} {M : Over S} {X : Over M.left}
variable (P : Projective.ProjectivePresentations.QuasiProjectivePresentation M) (Q : Projective.ProjectivePresentations.QuasiProjectivePresentation X)

def quasiProjectiveCompositeAmbient : Over S :=
  Projective.ProjectivePresentations.projectiveSpaceOver S Q.projective.dimension ⊗ P.compactification

def quasiProjectiveCompositeProjectivePresentation : Projective.ProjectivePresentations.ProjectivePresentation (quasiProjectiveCompositeAmbient P Q) :=
  (Projective.SpaceOverComposition.projectiveSpaceIdentityPresentation S Q.projective.dimension).product P.projective

def quasiProjectiveCompositeEmbedding : (Over.map M.hom).obj X ⟶ quasiProjectiveCompositeAmbient P Q :=
  (Over.map M.hom).map Q.embedding ≫ (Over.map M.hom).map Q.projective.embedding ≫
    (Projective.SpaceOverComposition.projectiveSpaceOverCompositionIso M Q.projective.dimension).hom ≫
      (𝟙 (Projective.ProjectivePresentations.projectiveSpaceOver S Q.projective.dimension) ⊗ₘ P.embedding)

theorem quasiProjectiveCompositeEmbedding_immersion : IsImmersion (quasiProjectiveCompositeEmbedding P Q).left := by
  have : IsOpenImmersion (𝟙 (Projective.ProjectivePresentations.projectiveSpaceOver S Q.projective.dimension) :
      Projective.ProjectivePresentations.projectiveSpaceOver S Q.projective.dimension ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S Q.projective.dimension).left :=
    inferInstanceAs (IsOpenImmersion (𝟙 (Projective.ProjectivePresentations.projectiveSpaceOver S Q.projective.dimension).left))
  have : IsOpenImmersion (𝟙 (Projective.ProjectivePresentations.projectiveSpaceOver S Q.projective.dimension) ⊗ₘ P.embedding).left :=
    QuasiProjectiveProducts.overTensorMap_open (𝟙 (Projective.ProjectivePresentations.projectiveSpaceOver S Q.projective.dimension)) P.embedding
  have : IsIso (Projective.SpaceOverComposition.projectiveSpaceOverCompositionIso M Q.projective.dimension).hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).map (Projective.SpaceOverComposition.projectiveSpaceOverCompositionIso M Q.projective.dimension).hom))
  have : IsOpenImmersion ((Over.map M.hom).map Q.embedding).left := Q.openImmersion
  have : IsClosedImmersion ((Over.map M.hom).map Q.projective.embedding).left := Q.projective.closedImmersion
  change IsImmersion (((Over.map M.hom).map Q.embedding).left ≫
    ((Over.map M.hom).map Q.projective.embedding).left ≫
      (Projective.SpaceOverComposition.projectiveSpaceOverCompositionIso M Q.projective.dimension).hom.left ≫
        (𝟙 (Projective.ProjectivePresentations.projectiveSpaceOver S Q.projective.dimension) ⊗ₘ P.embedding).left)
  infer_instance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.QuasiProjectiveCompositeImmersion
