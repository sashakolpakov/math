import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.Product
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Pullback.MorphismFiberEquality
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.VaryingDualReduction
import OAI.RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction

/-! # Pullback Morphism Reduction -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PullbackMorphismReduction

noncomputable section

/-! Equality of actual relative maps on their special fibers implies
equality on the native reduction in the actual product coordinates. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

variable (A B : Over Foundations.Scheme.ProjectiveSpace.complexBase) [GrpObj B]

theorem dualProductReduction_base :
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A).left ≫ (Pullback.Product.pullbackProductTotalIso (LieRanks.dualNumberTest ℂ) A).inv.left ≫
      ((Over.pullback (LieRanks.dualNumberTest ℂ).hom).obj A).hom = A.hom ≫ Smooth.AffineDualProduct.dualBaseReduction ℂ := by
  rw [Pullback.Product.pullbackProductTotalIso_inv_base]
  have h := congrArg (fun f => f.left)
    (lift_fst (toUnit A ≫ LieRanks.dualNumberOrigin ℂ) (𝟙 A))
  exact h

theorem dualPullbackMorphismEquiv_reduction
    (f g : (Over.pullback (LieRanks.dualNumberTest ℂ).hom).obj A ⟶ (Over.pullback (LieRanks.dualNumberTest ℂ).hom).obj B)
    (he : (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).map f = (Over.pullback (Smooth.AffineDualProduct.dualBaseReduction ℂ)).map g) :
    RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A ≫ Pullback.Product.pullbackProductMorphismEquiv (LieRanks.dualNumberTest ℂ) A B f =
      RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A ≫ Pullback.Product.pullbackProductMorphismEquiv (LieRanks.dualNumberTest ℂ) A B g := by
  let q := (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A).left ≫ (Pullback.Product.pullbackProductTotalIso (LieRanks.dualNumberTest ℂ) A).inv.left
  have hq : q ≫ ((Over.pullback (LieRanks.dualNumberTest ℂ).hom).obj A).hom = A.hom ≫ Smooth.AffineDualProduct.dualBaseReduction ℂ :=
    (Category.assoc _ _ _).trans (dualProductReduction_base A)
  have h := Pullback.MorphismFiberEquality.pullbackMorphism_eq_on_lift (Smooth.AffineDualProduct.dualBaseReduction ℂ) f g he q A.hom hq
  apply Over.OverMorphism.ext
  change (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A).left ≫ (Pullback.Product.pullbackProductMorphismEquiv (LieRanks.dualNumberTest ℂ) A B f).left =
    (RepresentationTheory.Theta.Geometric.Dual.BaseChangeReduction.dualBaseChangeReduction A).left ≫ (Pullback.Product.pullbackProductMorphismEquiv (LieRanks.dualNumberTest ℂ) A B g).left
  rw [Pullback.Product.pullbackProductMorphismEquiv_left, Pullback.Product.pullbackProductMorphismEquiv_left]
  exact (Category.assoc _ _ _).symm.trans
    (((Category.assoc _ _ _).symm.trans (congrArg (fun v => v ≫ pullback.fst B.hom (LieRanks.dualNumberTest ℂ).hom) h)).trans
      ((Category.assoc _ _ _).trans (Category.assoc _ _ _)))

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.PullbackMorphismReduction
