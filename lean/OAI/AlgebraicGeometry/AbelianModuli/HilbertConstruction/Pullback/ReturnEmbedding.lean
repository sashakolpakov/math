import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Projective.PresentationBaseChange

/-! # Return Embedding -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ReturnEmbedding

noncomputable section

/-! Shared base-change embeddings and their coefficient projections. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S T : Scheme.{u}} {X Y Z : Over S} {Q : Over T}

def pullbackReturnEmbedding (f : T ⟶ S) (j : X ⟶ Y) (a : Y ⟶ Z)
    (b : (Over.pullback f).obj Z ⟶ (Over.pullback f).obj Y)
    (c : Q ⟶ (Over.pullback f).obj X) : Q ⟶ (Over.pullback f).obj Y :=
  c ≫ ((Over.pullback f).map (j ≫ a) ≫ b)

theorem pullbackReturnEmbedding_closed (f : T ⟶ S) (j : X ⟶ Y) (a : Y ⟶ Z)
    (b : (Over.pullback f).obj Z ⟶ (Over.pullback f).obj Y)
    (c : Q ⟶ (Over.pullback f).obj X)
    [hj : IsClosedImmersion j.left] [ha : IsClosedImmersion a.left]
    [hb : IsClosedImmersion b.left] [hc : IsClosedImmersion c.left] :
    IsClosedImmersion (pullbackReturnEmbedding f j a b c).left := by
  have : IsClosedImmersion (j ≫ a).left := @IsClosedImmersion.comp _ _ _ _ _ hj ha
  exact @IsClosedImmersion.comp _ _ _ _ _ hc
    (@IsClosedImmersion.comp _ _ _ _ _ (Projective.PresentationBaseChange.overPullback_map_closed (j ≫ a) f) hb)

theorem pullbackReturnEmbedding_eq (f : T ⟶ S) (j : X ⟶ Y) (a : Y ⟶ Z)
    (b : (Over.pullback f).obj Z ⟶ (Over.pullback f).obj Y)
    (c : Q ⟶ (Over.pullback f).obj X)
    (h : (Over.pullback f).map a ≫ b = 𝟙 ((Over.pullback f).obj Y)) :
    pullbackReturnEmbedding f j a b c = c ≫ (Over.pullback f).map j := by
  unfold pullbackReturnEmbedding
  rw [Functor.map_comp, Category.assoc, h, Category.comp_id]

theorem pullbackReturnEmbedding_projection (f : T ⟶ S) (j : X ⟶ Y) (a : Y ⟶ Z)
    (b : (Over.pullback f).obj Z ⟶ (Over.pullback f).obj Y)
    (c : Q ⟶ (Over.pullback f).obj X)
    (h : (Over.pullback f).map a ≫ b = 𝟙 ((Over.pullback f).obj Y)) :
    (pullbackReturnEmbedding f j a b c).left ≫ pullback.fst Y.hom f =
      (c.left ≫ pullback.fst X.hom f) ≫ j.left := by
  rw [pullbackReturnEmbedding_eq f j a b c h]
  change (c.left ≫ ((Over.pullback f).map j).left) ≫ pullback.fst Y.hom f = _
  have hp : ((Over.pullback f).map j).left ≫ pullback.fst Y.hom f =
      pullback.fst X.hom f ≫ j.left := pullback.lift_fst _ _ _
  rw [Category.assoc, hp, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ReturnEmbedding
