import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase

/-! # Tensor Model -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorModel

noncomputable section

/-! The functor's inherited base action agrees with any compatible
module model, through an explicit algebra-linear tensor equivalence. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (S A : Type u) [CommRing S] [CommRing A] [Algebra S A]
  (M : Type u) [AddCommGroup M] [Module A M] [Module S M] [IsScalarTower S A M]
  (N : ModuleCat.{u} S)

local instance : Module A ((ModuleCat.restrictScalars (algebraMap S A)).obj (ModuleCat.of A M)) :=
  inferInstanceAs (Module A M)

local instance : IsScalarTower S A
    ((ModuleCat.restrictScalars (algebraMap S A)).obj (ModuleCat.of A M)) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def underlyingEquiv :
    (ModuleCat.restrictScalars (algebraMap S A)).obj (ModuleCat.of A M) ≃ₗ[A] M :=
  LinearEquiv.refl A M

def tensorModelEquiv :
    (TensorOverBase.tensorOverBase S A N).obj (ModuleCat.of A M) ≃ₗ[A] M ⊗[S] N :=
  @TensorProduct.AlgebraTensorModule.congr S A
    ((ModuleCat.restrictScalars (algebraMap S A)).obj (ModuleCat.of A M)) N M N
    _ _ _ _
    (TensorOverBase.moduleCarrier S A (ModuleCat.of A M)) _
    (TensorOverBase.scalarTowerCarrier S A (ModuleCat.of A M))
    _ _ _ _ _ _ _ _ (underlyingEquiv S A M) (LinearEquiv.refl S N)

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorModel
