import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.UnitParameters
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.UnitLawPullback

/-! # Left Unit Laws -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.LeftUnitLaws.Construction

noncomputable section

/-! The constructed horizontal and vertical Poincare products satisfy
the left unit law on every test scheme, without geometric restrictions
on the test scheme. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.Contraction

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

attribute [local instance] UnitParameters.Construction.poincareProductSpace_smooth UnitParameters.Construction.poincareProductSpace_proper UnitParameters.Construction.poincareProductSpace_connected

theorem poincareHorizontalUnit_end {T : Over (Spec (.of k))}
    (a x : T ⟶ UnitParameters.Construction.poincareProductSpace D) (ha : a ≫ fst D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a x x) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft (HorizontalProduct.Construction.poincareHorizontalProduct D a x x h) (AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) := by
  have hf := UnitParameters.Construction.horizontalUnitParameter_factor D a x ha h
  have hu := GroupUnitLaws.Construction.poincareHorizontalGroupUnit_end D (UnitParameters.Construction.horizontalUnitParameter D) (𝟙 (UnitParameters.Construction.poincareProductSpace D))
    (UnitParameters.Construction.horizontalUnitParameter_first D) (UnitParameters.Construction.horizontalUnitParameter_relation D)
  have hp := UnitLawPullback.Construction.contractedUnit_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x
    (UnitParameters.Construction.horizontalUnitParameter D) (𝟙 (UnitParameters.Construction.poincareProductSpace D)) a x hf (Category.comp_id x)
    (HorizontalProduct.Construction.poincareHorizontalProduct D (UnitParameters.Construction.horizontalUnitParameter D) (𝟙 _) (𝟙 _) (UnitParameters.Construction.horizontalUnitParameter_relation D))
    (AxisFrames.Construction.poincareHorizontalUnitFrame D (UnitParameters.Construction.horizontalUnitParameter D) (UnitParameters.Construction.horizontalUnitParameter_first D)).hom hu
  rw [HorizontalProduct.Construction.poincareHorizontalProduct_natural D x (UnitParameters.Construction.horizontalUnitParameter D) (𝟙 _) (𝟙 _)
      (UnitParameters.Construction.horizontalUnitParameter_relation D) a x x h hf (Category.comp_id x) (Category.comp_id x),
    AxisFrames.Construction.poincareHorizontalUnitFrame_natural D x (UnitParameters.Construction.horizontalUnitParameter D) a
      (UnitParameters.Construction.horizontalUnitParameter_first D) ha hf] at hp
  exact hp

theorem poincareHorizontalProduct_unit_left {T : Over (Spec (.of k))}
    (a x : T ⟶ UnitParameters.Construction.poincareProductSpace D) (ha : a ≫ fst D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a x x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (HorizontalProduct.Construction.poincareHorizontalProduct D a x x h).app U
      ((AxisFrames.Construction.poincareHorizontalUnitFrame D a ha).hom.app U (1 : Γ(T.left, U))) m = m :=
  (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_app _ _ U m).symm.trans (congrArg (fun f => f.app U m) (poincareHorizontalUnit_end D a x ha h))

theorem poincareVerticalUnit_end {T : Over (Spec (.of k))}
    (a x : T ⟶ UnitParameters.Construction.poincareProductSpace D) (ha : a ≫ snd D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a x x) :
    Picard.PoincareBundle.Bilinear.Contraction.contractLeft (VerticalProduct.Construction.poincareVerticalProduct D a x x h) (VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom =
      𝟙 (Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x) := by
  have hf := UnitParameters.Construction.verticalUnitParameter_factor D a x ha h
  have hu := GroupUnitLaws.Construction.poincareVerticalGroupUnit_end D (UnitParameters.Construction.verticalUnitParameter D) (𝟙 (UnitParameters.Construction.poincareProductSpace D))
    (UnitParameters.Construction.verticalUnitParameter_second D) (UnitParameters.Construction.verticalUnitParameter_relation D)
  have hp := UnitLawPullback.Construction.contractedUnit_pullback (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x
    (UnitParameters.Construction.verticalUnitParameter D) (𝟙 (UnitParameters.Construction.poincareProductSpace D)) a x hf (Category.comp_id x)
    (VerticalProduct.Construction.poincareVerticalProduct D (UnitParameters.Construction.verticalUnitParameter D) (𝟙 _) (𝟙 _) (UnitParameters.Construction.verticalUnitParameter_relation D))
    (VerticalUnits.Construction.poincareVerticalUnitFrame D (UnitParameters.Construction.verticalUnitParameter D) (UnitParameters.Construction.verticalUnitParameter_second D)).hom hu
  rw [VerticalProduct.Construction.poincareVerticalProduct_natural D x (UnitParameters.Construction.verticalUnitParameter D) (𝟙 _) (𝟙 _)
      (UnitParameters.Construction.verticalUnitParameter_relation D) a x x h hf (Category.comp_id x) (Category.comp_id x),
    VerticalUnits.Construction.poincareVerticalUnitFrame_natural D x (UnitParameters.Construction.verticalUnitParameter D) a
      (UnitParameters.Construction.verticalUnitParameter_second D) ha hf] at hp
  exact hp

theorem poincareVerticalProduct_unit_left {T : Over (Spec (.of k))}
    (a x : T ⟶ UnitParameters.Construction.poincareProductSpace D) (ha : a ≫ snd D.abelian.scheme A.scheme = 1)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a x x)
    (U : T.left.Opens) (m : Γ(Picard.PoincareBundle.Line.Fibers.fiber (Reference.PoincareLine.Construction.originalPoincarePoincareBundleLine D) x, U)) :
    (VerticalProduct.Construction.poincareVerticalProduct D a x x h).app U
      ((VerticalUnits.Construction.poincareVerticalUnitFrame D a ha).hom.app U (1 : Γ(T.left, U))) m = m :=
  (Picard.PoincareBundle.Bilinear.Contraction.contractLeft_app _ _ U m).symm.trans (congrArg (fun f => f.app U m) (poincareVerticalUnit_end D a x ha h))

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.LeftUnitLaws.Construction
