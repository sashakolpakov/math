import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.HorizontalAssociativity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.VerticalAssociativity
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.LeftUnitLaws
import OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Poincare.RightUnitLaws

/-! # Poincare Multiplications -/

namespace OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction

noncomputable section

/-! The original Poincare sheaf carries two fully constructed PoincareBundle
fiberwise multiplications. Every field is supplied by a proved law of
the actual products and frames; no multiplication is an extra input. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

open OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication

variable {k : Type} [Field k] [IsAlgClosed k] {g : ℕ}
  {A : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g (Spec (.of k))} (D : AbelianModuli.HilbertConstruction.Dual.Data.DualAbelianData A)

def originalPoincareHorizontalMultiplication :
    Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) (PoincareLine.Construction.originalPoincarePoincareBundleLine D) where
  product := Poincare.HorizontalProduct.Construction.poincareHorizontalProduct D
  product_isIso := Poincare.HorizontalProduct.Construction.poincareHorizontalProduct_isIso D
  unitFrame := Poincare.AxisFrames.Construction.poincareHorizontalUnitFrame D
  unit_left := Poincare.LeftUnitLaws.Construction.poincareHorizontalProduct_unit_left D
  unit_right := Poincare.RightUnitLaws.Construction.poincareHorizontalProduct_unit_right D
  associative := Poincare.HorizontalAssociativity.Construction.poincareHorizontalProduct_associative D
  product_natural := Poincare.HorizontalProduct.Construction.poincareHorizontalProduct_natural D
  unit_natural := Poincare.AxisFrames.Construction.poincareHorizontalUnitFrame_natural D

def originalPoincareVerticalMultiplication :
    Picard.PoincareBundle.FiberwiseMultiplication.Multiplication (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) (PoincareLine.Construction.originalPoincarePoincareBundleLine D) where
  product := Poincare.VerticalProduct.Construction.poincareVerticalProduct D
  product_isIso := Poincare.VerticalProduct.Construction.poincareVerticalProduct_isIso D
  unitFrame := Poincare.VerticalUnits.Construction.poincareVerticalUnitFrame D
  unit_left := Poincare.LeftUnitLaws.Construction.poincareVerticalProduct_unit_left D
  unit_right := Poincare.RightUnitLaws.Construction.poincareVerticalProduct_unit_right D
  associative := Poincare.VerticalAssociativity.Construction.poincareVerticalProduct_associative D
  product_natural := Poincare.VerticalProduct.Construction.poincareVerticalProduct_natural D
  unit_natural := Poincare.VerticalUnits.Construction.poincareVerticalUnitFrame_natural D

theorem originalPoincareHorizontalMultiplication_product {T : Over (Spec (.of k))}
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (fst D.abelian.scheme A.scheme) (snd D.abelian.scheme A.scheme) a b c) :
    (originalPoincareHorizontalMultiplication D).product a b c h = Poincare.HorizontalProduct.Construction.poincareHorizontalProduct D a b c h := rfl

theorem originalPoincareVerticalMultiplication_product {T : Over (Spec (.of k))}
    (a b c : T ⟶ D.abelian.scheme ⊗ A.scheme)
    (h : Picard.PoincareBundle.FiberwiseMultiplication.ProductRel (snd D.abelian.scheme A.scheme) (fst D.abelian.scheme A.scheme) a b c) :
    (originalPoincareVerticalMultiplication D).product a b c h = Poincare.VerticalProduct.Construction.poincareVerticalProduct D a b c h := rfl

theorem originalPoincareMultiplications_unit_zero (T : Over (Spec (.of k))) :
    (originalPoincareHorizontalMultiplication D).unitFrame (1 : T ⟶ D.abelian.scheme ⊗ A.scheme)
      (MonObj.one_comp (fst D.abelian.scheme A.scheme)) =
    (originalPoincareVerticalMultiplication D).unitFrame (1 : T ⟶ D.abelian.scheme ⊗ A.scheme)
      (MonObj.one_comp (snd D.abelian.scheme A.scheme)) :=
  Poincare.VerticalUnits.Construction.poincareUnitFrames_agree_at_zero D T

end

end OAI.AlgebraicGeometry.AbelianScheme.IsogenyQuotient.Reference.PoincareMultiplications.Construction
