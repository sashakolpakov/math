import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.FixedDimension.Family

/-! # Base Change Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective

noncomputable section

open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u

theorem ProjectivePresentations.ProjectivePresentation.baseChange_embedding {S T : Scheme.{u}} {X : Over S}
    (P : ProjectivePresentations.ProjectivePresentation X) (f : T ⟶ S) :
    (P.baseChange f).embedding = CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnMap (Over.pullback f)
      P.embedding (SpaceBaseChange.projectiveSpaceOverBaseChangeIso f P.dimension) := rfl

theorem BaseChangeEmbedding.fixedDimensionHilbertUniversalProjectivePresentation_dimension (S : Scheme.{u})
    (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).dimension = n := rfl

theorem BaseChangeEmbedding.fixedDimensionHilbertUniversalProjectivePresentation_embedding (S : Scheme.{u})
    (n : ℕ) (P : Polynomial ℚ) (g : ℕ) :
    (FixedDimension.Family.fixedDimensionHilbertUniversalProjectivePresentation S n P g).embedding =
      (FixedDimension.Parameters.fixedDimensionHilbertUniversalFamily S n P g).family.inclusion := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective
