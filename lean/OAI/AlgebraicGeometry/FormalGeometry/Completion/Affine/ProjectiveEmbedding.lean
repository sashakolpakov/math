import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

/-! # Projective Embedding -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ProjectiveEmbedding

noncomputable section

/-! Over an affine base, an actual projective presentation gives an actual
closed immersion into polynomial projective space over the ring of base functions. -/

set_option backward.isDefEq.respectTransparency false

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations

namespace Construction

universe u

def projectiveAffineEmbedding {S : Scheme.{u}} (A : Over S)
    (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) :
    A.left ⟶ (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) P.dimension).left :=
  P.embedding.left ≫ pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) P.dimension).hom S.toSpecΓ

instance projectiveAffineEmbedding_isClosedImmersion {S : Scheme.{u}} [IsAffine S]
    (A : Over S) (P : AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.ProjectivePresentation A) :
    IsClosedImmersion (projectiveAffineEmbedding A P) := by
  have : IsClosedImmersion P.embedding.left := P.closedImmersion
  have : IsIso (pullback.fst (AbelianModuli.HilbertConstruction.Projective.ProjectivePresentations.affineProjectiveSpace Γ(S, ⊤) P.dimension).hom S.toSpecΓ) :=
    inferInstance
  unfold projectiveAffineEmbedding
  exact IsClosedImmersion.comp P.embedding.left _

end Construction

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.Affine.ProjectiveEmbedding
