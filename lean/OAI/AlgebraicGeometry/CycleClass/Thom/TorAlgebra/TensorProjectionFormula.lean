import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorModel
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RestrictionProjectives

/-! # Tensor Projection Formula -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorProjectionFormula

noncomputable section

/-! Tensoring an algebra module over its base commutes with tensoring
over the algebra. The comparison is the native tensor associator after
identifying the inherited base action. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorModel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (N : ModuleCat.{u} R)

attribute [local instance] TensorOverBase.moduleCarrier
  TensorOverBase.scalarTowerCarrier

def assocComponent (P X : ModuleCat.{u} A) :
    (TensorOverBase.tensorOverBase R A N).obj ((tensorRight P).obj X) ≃ₗ[A]
      (tensorRight ((TensorOverBase.tensorOverBase R A N).obj P)).obj X :=
  (TensorModel.tensorModelEquiv R A (X ⊗[A] P) N).trans
    (TensorProduct.AlgebraTensorModule.assoc R A A X P N)

def tensorAssocIso (P : ModuleCat.{u} A) :
    tensorRight P ⋙ TensorOverBase.tensorOverBase R A N ≅ tensorRight ((TensorOverBase.tensorOverBase R A N).obj P) :=
  NatIso.ofComponents (fun X => (assocComponent R A N P X).toModuleIso) (by
    intro X Y f
    ext t
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul t n =>
      induction t using TensorProduct.inductionOn with
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]
      | tmul x p => rfl)

def tensorUnitIso : tensorRight (ModuleCat.of A A) ≅ 𝟭 (ModuleCat.{u} A) :=
  RestrictionProjectives.tensorUnitIso A A

def tensorRepresentationIso :
    TensorOverBase.tensorOverBase R A N ≅ tensorRight ((TensorOverBase.tensorOverBase R A N).obj (ModuleCat.of A A)) :=
  (Functor.leftUnitor _).symm ≪≫
  Functor.isoWhiskerRight (tensorUnitIso A).symm (TensorOverBase.tensorOverBase R A N) ≪≫
  tensorAssocIso R A N (ModuleCat.of A A)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorProjectionFormula
