import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBaseProjectives
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorModel
import OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightAlgebra
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # External Tensor Projectives -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorProjectives

noncomputable section

/-! Over a field, tensoring over the right algebra factor and
restricting to the left factor preserves projective modules. The free
generator becomes the actual scalar extension of the second module. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBaseProjectives OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorModel
open OAI.AlgebraicGeometry.CycleClass.Thom.Tensor.ProductRightAlgebra.Constructions

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R S : Type u) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
  (N : ModuleCat.{u} S)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

local instance : Module k N := Module.compHom N (algebraMap k S)
local instance : IsScalarTower k S N := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

def externalTensor : ModuleCat.{u} (R ⊗[k] S) ⥤ ModuleCat.{u} R :=
  TensorOverBaseProjectives.tensorRestriction S (R ⊗[k] S) R N

theorem model_smul (r : R)
    (t : (TensorOverBase.tensorOverBase S (R ⊗[k] S) N).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) :
    TensorModel.tensorModelEquiv S (R ⊗[k] S) (R ⊗[k] S) N (algebraMap R (R ⊗[k] S) r • t) =
      r • TensorModel.tensorModelEquiv S (R ⊗[k] S) (R ⊗[k] S) N t := by
  rw [map_smul]
  exact IsScalarTower.algebraMap_smul (R ⊗[k] S) r _

def freeModelEquiv :
    (externalTensor k R S N).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S)) ≃ₗ[R]
      (R ⊗[k] S) ⊗[S] N where
  __ := (TensorModel.tensorModelEquiv S (R ⊗[k] S) (R ⊗[k] S) N).toAddEquiv
  map_smul' := model_smul k R S N

def freeTensorEquiv :
    (externalTensor k R S N).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S)) ≃ₗ[R] R ⊗[k] N :=
  (freeModelEquiv k R S N).trans (Tensor.ProductRightAlgebra.Constructions.leftLinearCancel k R S N)

instance free_projective :
    Projective ((externalTensor k R S N).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) := by
  let : Module.Projective k N := inferInstance
  let : Module.Projective R (R ⊗[k] N) := inferInstance
  let : Module.Projective R ((externalTensor k R S N).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) :=
    Module.Projective.of_equiv' (freeTensorEquiv k R S N).symm
  infer_instance

instance externalTensor_preservesProjectiveObjects : (externalTensor k R S N).PreservesProjectiveObjects := by
  let : Projective ((TensorOverBaseProjectives.tensorRestriction S (R ⊗[k] S) R N).obj (ModuleCat.of (R ⊗[k] S) (R ⊗[k] S))) :=
    free_projective k R S N
  exact TensorOverBaseProjectives.tensorRestriction_preservesProjectiveObjects S (R ⊗[k] S) R N

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorProjectives
