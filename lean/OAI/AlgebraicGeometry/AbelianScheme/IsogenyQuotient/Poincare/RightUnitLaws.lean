import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.UnitParameters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.GroupRightUnits
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Product.RelationSwap

/-! # Right Unit Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.RightUnitLaws.Construction

noncomputable section

/-! The original horizontal and vertical Poincare products satisfy
the right-unit law on every test scheme, by pulling back the proper
universal unit configuration. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

attribute [local instance] UnitParameters.Construction.poincareProductSpace_smooth UnitParameters.Construction.poincareProductSpace_proper UnitParameters.Construction.poincareProductSpace_connected

theorem poincareHorizontalRightUnit_end {T : Over (Spec (.of k))}
    (x a : T ⟶ UnitParameters.Construction.poincareProductSpace D) (ha : a ≫ fst D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) x a x) :
    RightContraction.Construction.lineContractRight (HorizontalProduct.Construction.poincareHorizontalProduct D x a x h) (AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) := by
  have hf := UnitParameters.Construction.horizontalUnitParameter_factor D a x ha (Product.RelationSwap.Construction.productRel_swap h)
  have hu := GroupRightUnits.Construction.poincareHorizontalGroupRightUnit_end D (𝟙 (UnitParameters.Construction.poincareProductSpace D)) (UnitParameters.Construction.horizontalUnitParameter D)
    (UnitParameters.Construction.horizontalUnitParameter_first D) (Product.RelationSwap.Construction.productRel_swap (UnitParameters.Construction.horizontalUnitParameter_relation D))
  have hp := RightContraction.Construction.contractedRightUnit_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x
    (𝟙 (UnitParameters.Construction.poincareProductSpace D)) (UnitParameters.Construction.horizontalUnitParameter D) x a (Category.comp_id x) hf
    (HorizontalProduct.Construction.poincareHorizontalProduct D (𝟙 _) (UnitParameters.Construction.horizontalUnitParameter D) (𝟙 _)
      (Product.RelationSwap.Construction.productRel_swap (UnitParameters.Construction.horizontalUnitParameter_relation D)))
    (AxisFrames.Construction.poincareHorizontalUnitFrame D (UnitParameters.Construction.horizontalUnitParameter D) (UnitParameters.Construction.horizontalUnitParameter_first D)).hom hu
  rw [HorizontalProduct.Construction.poincareHorizontalProduct_natural D x (𝟙 _) (UnitParameters.Construction.horizontalUnitParameter D) (𝟙 _)
      (Product.RelationSwap.Construction.productRel_swap (UnitParameters.Construction.horizontalUnitParameter_relation D)) x a x h (Category.comp_id x) hf (Category.comp_id x),
    AxisFrames.Construction.poincareHorizontalUnitFrame_natural D x (UnitParameters.Construction.horizontalUnitParameter D) a
      (UnitParameters.Construction.horizontalUnitParameter_first D) ha hf] at hp
  exact hp

theorem poincareHorizontalProduct_unit_right {T : Over (Spec (.of k))}
    (x a : T ⟶ UnitParameters.Construction.poincareProductSpace D) (ha : a ≫ fst D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) x a x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (HorizontalProduct.Construction.poincareHorizontalProduct D x a x h).app U m
      ((AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom.app U (1 : Γ(T.left, U))) = m :=
  (RightContraction.Construction.lineContractRight_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (poincareHorizontalRightUnit_end D x a ha h))

theorem poincareVerticalRightUnit_end {T : Over (Spec (.of k))}
    (x a : T ⟶ UnitParameters.Construction.poincareProductSpace D) (ha : a ≫ snd D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) x a x) :
    RightContraction.Construction.lineContractRight (VerticalProduct.Construction.poincareVerticalProduct D x a x h) (VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) := by
  have hf := UnitParameters.Construction.verticalUnitParameter_factor D a x ha (Product.RelationSwap.Construction.productRel_swap h)
  have hu := GroupRightUnits.Construction.poincareVerticalGroupRightUnit_end D (𝟙 (UnitParameters.Construction.poincareProductSpace D)) (UnitParameters.Construction.verticalUnitParameter D)
    (UnitParameters.Construction.verticalUnitParameter_second D) (Product.RelationSwap.Construction.productRel_swap (UnitParameters.Construction.verticalUnitParameter_relation D))
  have hp := RightContraction.Construction.contractedRightUnit_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x
    (𝟙 (UnitParameters.Construction.poincareProductSpace D)) (UnitParameters.Construction.verticalUnitParameter D) x a (Category.comp_id x) hf
    (VerticalProduct.Construction.poincareVerticalProduct D (𝟙 _) (UnitParameters.Construction.verticalUnitParameter D) (𝟙 _)
      (Product.RelationSwap.Construction.productRel_swap (UnitParameters.Construction.verticalUnitParameter_relation D)))
    (VerticalUnits.Construction.poincareVerticalUnitFrame D (UnitParameters.Construction.verticalUnitParameter D) (UnitParameters.Construction.verticalUnitParameter_second D)).hom hu
  rw [VerticalProduct.Construction.poincareVerticalProduct_natural D x (𝟙 _) (UnitParameters.Construction.verticalUnitParameter D) (𝟙 _)
      (Product.RelationSwap.Construction.productRel_swap (UnitParameters.Construction.verticalUnitParameter_relation D)) x a x h (Category.comp_id x) hf (Category.comp_id x),
    VerticalUnits.Construction.poincareVerticalUnitFrame_natural D x (UnitParameters.Construction.verticalUnitParameter D) a
      (UnitParameters.Construction.verticalUnitParameter_second D) ha hf] at hp
  exact hp

theorem poincareVerticalProduct_unit_right {T : Over (Spec (.of k))}
    (x a : T ⟶ UnitParameters.Construction.poincareProductSpace D) (ha : a ≫ snd D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) x a x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (VerticalProduct.Construction.poincareVerticalProduct D x a x h).app U m
      ((VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom.app U (1 : Γ(T.left, U))) = m :=
  (RightContraction.Construction.lineContractRight_app _ _ U m).symm.trans
    (congrArg (fun f => f.app U m) (poincareVerticalRightUnit_end D x a ha h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.RightUnitLaws.Construction
