import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairBaseChangeProjection

/-! # Pair Cover Projection -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairCoverProjection

noncomputable section

/-! Equality with the native product projection is detected by its
two component equations. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u

theorem pairBaseChangeProjection_comp_eq {S T Z : Scheme.{u}} (b : T ⟶ S) (D A : Over S)
    (k : Z ⟶ ((Over.pullback b).obj D ⊗ (Over.pullback b).obj A).left)
    (q : Z ⟶ (D ⊗ A).left)
    (hD : k ≫ (fst ((Over.pullback b).obj D) ((Over.pullback b).obj A)).left ≫
      pullback.fst D.hom b = q ≫ (fst D A).left)
    (hA : k ≫ (snd ((Over.pullback b).obj D) ((Over.pullback b).obj A)).left ≫
      pullback.fst A.hom b = q ≫ (snd D A).left) :
    k ≫ PairBaseChangeProjection.pairBaseChangeProjection b D A = q := by
  apply Over.tensorObj_ext
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => k ≫ z) (PairBaseChangeProjection.pairBaseChangeProjection_fst b D A)).trans hD)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun z => k ≫ z) (PairBaseChangeProjection.pairBaseChangeProjection_snd b D A)).trans hA)

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairCoverProjection
