import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.RelativeProjective.GraphRecovery
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Graph.FamilyNaturality

/-! # Graph Embedding Cartesian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbeddingCartesian

noncomputable section

/-! The relative projective graph embedding is the actual Cartesian base change of the fixed product embedding. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

universe u

variable {S T : Scheme.{u}} {A B : Over S} {n : ℕ} (f : T ⟶ S)
variable (j : A ⊗ B ⟶ Projective.ProjectivePresentations.projectiveSpaceOver S n)

theorem relativeProjectiveGraphEmbedding_over :
    (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j).left ≫ RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n =
      Graph.FamilyNaturality.overProductBaseChangeMap f A B ≫ j.left := by
  let hp := RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n
  have he := congrArg Over.Hom.left
    (Cartesian.PullbackGraphEmbedding.cartesianPullbackGraphEmbedding_comp (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) f hp j)
  have h := congrArg (fun k => k ≫ pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom f) he
  change ((RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j).left ≫ hp.isoPullback.hom) ≫
      pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom f =
    ((Functor.Monoidal.μIso (Over.pullback f) A B).hom.left ≫ ((Over.pullback f).map j).left) ≫
      pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom f at h
  have hj : ((Over.pullback f).map j).left ≫ pullback.fst (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom f =
      pullback.fst (A ⊗ B).hom f ≫ j.left := pullback.lift_fst _ _ _
  rw [Category.assoc, hp.isoPullback_hom_fst, Category.assoc, hj, ← Category.assoc] at h
  exact h

theorem relativeProjectiveGraphEmbedding_isPullback :
    IsPullback (RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j).left (Graph.FamilyNaturality.overProductBaseChangeMap f A B)
      (RelativeProjective.BaseMaps.relativeProjectiveBaseMap f n) j.left := by
  have houter : IsPullback (Graph.FamilyNaturality.overProductBaseChangeMap f A B)
      ((RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j).left ≫ (Projective.ProjectivePresentations.projectiveSpaceOver T n).hom)
      (j.left ≫ (Projective.ProjectivePresentations.projectiveSpaceOver S n).hom) f := by
    rw [(RelativeProjective.GraphRecovery.relativeProjectiveGraphEmbedding f j).w, j.w]
    exact Graph.FamilyNaturality.overProductBaseChange_isPullback f A B
  exact (houter.of_bot (relativeProjectiveGraphEmbedding_over f j).symm
    (RelativeProjective.BaseMaps.relativeProjectiveBaseMap_isPullback f n)).flip

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Relative.GraphEmbeddingCartesian
