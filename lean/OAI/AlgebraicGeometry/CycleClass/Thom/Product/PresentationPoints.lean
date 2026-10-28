import OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct
import OAI.AlgebraicGeometry.CycleClass.Thom.Product.SupportScheme

/-! # Presentation Points -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions

noncomputable section

/-! Actual complex points of an arbitrary limiting product presentation,
with the native projection maps and genuine point pairing. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.CartesianMonoidalCategory
open scoped MonoidalCategory

open OAI.AlgebraicGeometry.CycleClass.Thom.Scheme.PointProduct.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X Y Z : Over Foundations.Scheme.ProjectiveSpace.complexBase) (πX : Z ⟶ X) (πY : Z ⟶ Y)
  (hprod : IsLimit (BinaryFan.mk πX πY))

def productPresentationPairMap : X ⊗ Y ⟶ Z :=
  BinaryFan.IsLimit.lift hprod (fst X Y) (snd X Y)

@[reassoc (attr := simp)]
theorem productPresentationPairMap_fst :
    productPresentationPairMap X Y Z πX πY hprod ≫ πX = fst X Y :=
  BinaryFan.IsLimit.lift_fst hprod _ _

@[reassoc (attr := simp)]
theorem productPresentationPairMap_snd :
    productPresentationPairMap X Y Z πX πY hprod ≫ πY = snd X Y :=
  BinaryFan.IsLimit.lift_snd hprod _ _

def productPresentationPointsHomeomorph :
    ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z ≃ₜ (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints X × ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Y) where
  toFun p := (p ≫ πX, p ≫ πY)
  invFun xy := lift xy.1 xy.2 ≫ productPresentationPairMap X Y Z πX πY hprod
  left_inv p := by
    apply BinaryFan.IsLimit.hom_ext hprod
    · change (lift (p ≫ πX) (p ≫ πY) ≫ productPresentationPairMap X Y Z πX πY hprod) ≫ πX = p ≫ πX
      rw [Category.assoc, productPresentationPairMap_fst X Y Z πX πY hprod, lift_fst]
    · change (lift (p ≫ πX) (p ≫ πY) ≫ productPresentationPairMap X Y Z πX πY hprod) ≫ πY = p ≫ πY
      rw [Category.assoc, productPresentationPairMap_snd X Y Z πX πY hprod, lift_snd]
  right_inv xy := by simp only [Category.assoc, productPresentationPairMap_fst,
    productPresentationPairMap_snd, lift_fst, lift_snd]
  continuous_toFun := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πX).prodMk
    (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map πY)
  continuous_invFun := (ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints.continuous_map
    (productPresentationPairMap X Y Z πX πY hprod)).comp (Scheme.PointProduct.Constructions.schemePointPair_continuous X Y)

@[simp]
theorem productPresentationPointsHomeomorph_apply (z : ComplexPoints.Analytic.SchemePointHomeomorphs.schemeComplexPoints Z) :
    productPresentationPointsHomeomorph X Y Z πX πY hprod z = (z ≫ πX, z ≫ πY) := rfl

end

end OAI.AlgebraicGeometry.CycleClass.Thom.Product.PresentationPoints.Constructions
