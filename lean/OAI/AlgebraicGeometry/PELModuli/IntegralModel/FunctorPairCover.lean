import OAI.AlgebraicGeometry.PELModuli.IntegralModel.FunctorPairComparison
import OAI.AlgebraicGeometry.PELModuli.IntegralModel.PairCoverProjection

/-! # Functor Pair Cover -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.FunctorPairCover

noncomputable section

/-! The cover of a product is determined by the two prescribed
cartesian family comparisons and their actual projection equations. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

universe u v w

theorem functorPairComparison_cover
    {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
    {S T : Scheme.{w}} (b : T ⟶ S) (F : C ⥤ Over T) [F.Monoidal] (D A : C)
    (D' A' : Over S)
    (eD : F.obj D ≅ (Over.pullback b).obj D') (eA : F.obj A ≅ (Over.pullback b).obj A')
    (qd : (F.obj D).left ⟶ D'.left) (qa : (F.obj A).left ⟶ A'.left)
    (q : (F.obj (D ⊗ A)).left ⟶ (D' ⊗ A').left)
    (hd : eD.hom.left ≫ pullback.fst D'.hom b = qd)
    (ha : eA.hom.left ≫ pullback.fst A'.hom b = qa)
    (hq₁ : q ≫ (fst D' A').left = (F.map (fst D A)).left ≫ qd)
    (hq₂ : q ≫ (snd D' A').left = (F.map (snd D A)).left ≫ qa) :
    (FunctorPairComparison.functorPairComparison F D A eD eA).hom.left ≫ PairBaseChangeProjection.pairBaseChangeProjection b D' A' = q := by
  have hf := congrArg Over.Hom.left (FunctorPairComparison.functorPairComparison_fst F D A eD eA)
  have hs := congrArg Over.Hom.left (FunctorPairComparison.functorPairComparison_snd F D A eD eA)
  apply PairCoverProjection.pairBaseChangeProjection_comp_eq b D' A'
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ pullback.fst D'.hom b) hf).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => (F.map (fst D A)).left ≫ z) hd).trans hq₁.symm)))
  · exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ pullback.fst A'.hom b) hs).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => (F.map (snd D A)).left ≫ z) ha).trans hq₂.symm)))

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.FunctorPairCover
