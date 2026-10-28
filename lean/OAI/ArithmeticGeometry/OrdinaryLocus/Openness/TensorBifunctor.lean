import OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorUnit
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Products.Basic

/-! # Tensor Bifunctor -/

namespace OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorBifunctor.Construction

noncomputable section

/-! Tensor comparison squares and their adjunctions. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u v

def tensorSheafFunctor (X : Scheme.{u}) : (X.Modules × X.Modules) ⥤ X.Modules where
  obj M := SheafTensor.Construction.sheafTensor M.1 M.2
  map f := TensorFunctoriality.Construction.sheafTensorMap f.1 f.2
  map_id M := TensorFunctoriality.Construction.sheafTensorMap_id M.1 M.2
  map_comp f g := TensorFunctoriality.Construction.sheafTensorMap_comp f.1 g.1 f.2 g.2

def pushforwardTensorNat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pushforward f).prod (Scheme.Modules.pushforward f) ⋙ tensorSheafFunctor Y ⟶
      tensorSheafFunctor X ⋙ Scheme.Modules.pushforward f where
  app M := TensorFunctoriality.Construction.pushforwardSheafTensorMap f M.1 M.2
  naturality _M _N g := (TensorFunctoriality.Construction.pushforwardSheafTensorMap_naturality f g.1 g.2).symm

def pullbackTensorNat {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorSheafFunctor Y ⋙ Scheme.Modules.pullback f ⟶
      (Scheme.Modules.pullback f).prod (Scheme.Modules.pullback f) ⋙ tensorSheafFunctor X where
  app M := TensorFunctoriality.Construction.pullbackSheafTensorMap f M.1 M.2
  naturality _M _N g := TensorFunctoriality.Construction.pullbackSheafTensorMap_naturality f g.1 g.2

def productAdjunction
    {C D E F : Type v} [Category.{u} C] [Category.{u} D] [Category.{u} E] [Category.{u} F]
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) : L₁.prod L₂ ⊣ R₁.prod R₂ where
  unit :=
    { app X := (a.unit.app X.1, b.unit.app X.2)
      naturality _X _Y f := Prod.ext (a.unit.naturality f.1) (b.unit.naturality f.2) }
  counit :=
    { app X := (a.counit.app X.1, b.counit.app X.2)
      naturality _X _Y f := Prod.ext (a.counit.naturality f.1) (b.counit.naturality f.2) }
  left_triangle_components X := Prod.ext (a.left_triangle_components X.1) (b.left_triangle_components X.2)
  right_triangle_components X := Prod.ext (a.right_triangle_components X.1) (b.right_triangle_components X.2)

def pullbackTensorSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TwoSquare (tensorSheafFunctor Y)
      ((Scheme.Modules.pullback f).prod (Scheme.Modules.pullback f))
      (Scheme.Modules.pullback f) (tensorSheafFunctor X) :=
  TwoSquare.mk _ _ _ _ (pullbackTensorNat f)

def pushforwardTensorSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TwoSquare ((Scheme.Modules.pushforward f).prod (Scheme.Modules.pushforward f))
      (tensorSheafFunctor X) (tensorSheafFunctor Y) (Scheme.Modules.pushforward f) :=
  TwoSquare.mk _ _ _ _ (pushforwardTensorNat f)

theorem pullbackTensorSquare_eq_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSquare f =
      (mateEquiv (productAdjunction (Scheme.Modules.pullbackPushforwardAdjunction f)
        (Scheme.Modules.pullbackPushforwardAdjunction f))
        (Scheme.Modules.pullbackPushforwardAdjunction f)).symm (pushforwardTensorSquare f) := by
  apply TwoSquare.ext
  intro M
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (TensorFunctoriality.Construction.pullbackSheafTensorMap f M.1 M.2) = _
  rw [TensorFunctoriality.Construction.pullbackSheafTensorMap, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  exact unit_mateEquiv_symm
    (productAdjunction (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction f) (pushforwardTensorSquare f) M

theorem mate_pullbackTensorSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    mateEquiv (productAdjunction (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackPushforwardAdjunction f) (pullbackTensorSquare f) =
      pushforwardTensorSquare f := by
  rw [pullbackTensorSquare_eq_mate, Equiv.apply_symm_apply]

theorem conjugateEquiv_product_pullbackComp_inv {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv
      ((productAdjunction (Scheme.Modules.pullbackPushforwardAdjunction g)
        (Scheme.Modules.pullbackPushforwardAdjunction g)).comp
        (productAdjunction (Scheme.Modules.pullbackPushforwardAdjunction f)
          (Scheme.Modules.pullbackPushforwardAdjunction f)))
      (productAdjunction (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
        (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)))
      (NatTrans.prod (Scheme.Modules.pullbackComp f g).inv
        (Scheme.Modules.pullbackComp f g).inv) =
      NatTrans.prod (Scheme.Modules.pushforwardComp f g).hom
        (Scheme.Modules.pushforwardComp f g).hom := by
  apply NatTrans.ext
  funext M
  apply Prod.ext
  · change (conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      (Scheme.Modules.pullbackComp f g).inv).app M.1 = _
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv]
    rfl
  · change (conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      (Scheme.Modules.pullbackComp f g).inv).app M.2 = _
    rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv]
    rfl

end

end OAI.ArithmeticGeometry.OrdinaryLocus.Openness.TensorBifunctor.Construction
