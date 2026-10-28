import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Embedded.GraphIsomorphismTransport
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.Products

/-! # Embedding Compatibility -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.EmbeddingCompatibility

noncomputable section

/-! Compatible factor embeddings give compatible native Segre product
embeddings. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {S : Scheme.{u}} {X X' Y Y' : Over S} {n m : ℕ}

theorem projectiveProductEmbedding_compatible
    (a : X ⟶ X') (b : Y ⟶ Y')
    (i : X ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j : Y ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S m)
    (i' : X' ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) (j' : Y' ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S m)
    (hi : a ≫ i' = i) (hj : b ≫ j' = j) :
    (a ⊗ₘ b) ≫ ((i' ⊗ₘ j') ≫ (Projective.Products.projectiveSpaceProductPresentation S n m).embedding) =
      (i ⊗ₘ j) ≫ (Projective.Products.projectiveSpaceProductPresentation S n m).embedding := by
  rw [← Category.assoc, tensorHom_comp_tensorHom, hi, hj]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Segre.EmbeddingCompatibility
