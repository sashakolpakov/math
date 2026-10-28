import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Product.ParameterTensorIso

/-! # Graph Embedding Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbeddingComposition

noncomputable section

/-! Successive relative projective product embeddings agree with the direct embedding after the geometric source and target comparison isomorphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

theorem relativeProjectiveGraphEmbedding_parameter_composition
    {S : Scheme.{u}} {T M : Over S} {A B : Over S} {n : ℕ}
    (f : T ⟶ M) (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n) :
    ((Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom ⊗ₘ (Single.ParameterBaseChange.singleParameterBaseChangeIso f B).hom) ≫
      RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f.left (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j) =
        RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding T.hom j := by
  apply (cancel_mono (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f.left n) f.left
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f.left n)).hom).mp
  rw [Category.assoc]
  change ((Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom ⊗ₘ (Single.ParameterBaseChange.singleParameterBaseChangeIso f B).hom) ≫
      (Cartesian.PullbackGraphEmbedding.cartesianPullbackGraphEmbedding (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f.left n) f.left
        (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f.left n) (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j) ≫
          (ClosedFamily.PullbackRecoveryIso.cartesianAmbientOverIso (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f.left n) f.left
            (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f.left n)).hom) = _
  rw [Cartesian.PullbackGraphEmbedding.cartesianPullbackGraphEmbedding_comp]
  change ((Single.ParameterBaseChange.singleParameterBaseChangeIso f A).hom ⊗ₘ (Single.ParameterBaseChange.singleParameterBaseChangeIso f B).hom) ≫
    ((Functor.Monoidal.μIso (Over.pullback f.left) ((Over.pullback M.hom).obj A) ((Over.pullback M.hom).obj B)).hom ≫
      (Over.pullback f.left).map (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding M.hom j)) = _
  rw [← Category.assoc, Product.ParameterTensorIso.productParameterBaseChangeIso_tensor, Product.ParameterIsoCompatibility.productParameterBaseChangeIso_embedding]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbeddingComposition
