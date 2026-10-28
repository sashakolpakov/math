import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.ReturnEmbedding
import OAI.CategoryTheory.Functors.FunctorReturnIsomorphism

/-! # Named Return Projection -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NamedReturnProjection

noncomputable section

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable {S T : Scheme.{u}} {X Y : Over S} {Q : Over T}
theorem pullbackReturnEmbedding_projection_named
    (f : T ⟶ S) (j : X ⟶ Y) {Z : Over S} (a : Y ⟶ Z)
    (k : (Over.pullback f).obj Y ≅ (Over.pullback f).obj Z)
    (c : Q ⟶ (Over.pullback f).obj X)
    (h : CategoryTheory.Functors.FunctorReturnIsomorphism.functorReturnMap (Over.pullback f) a k =
      𝟙 ((Over.pullback f).obj Y)) :
    (Pullback.ReturnEmbedding.pullbackReturnEmbedding f j a k.inv c).left ≫ pullback.fst Y.hom f =
      (c.left ≫ pullback.fst X.hom f) ≫ j.left :=
  Pullback.ReturnEmbedding.pullbackReturnEmbedding_projection f j a k.inv c h

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NamedReturnProjection
