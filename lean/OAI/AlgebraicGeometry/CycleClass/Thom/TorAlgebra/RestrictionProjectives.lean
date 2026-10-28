import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBaseProjectives
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact

/-! # Restriction Projectives -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RestrictionProjectives

noncomputable section

/-! Restriction of scalars preserves projectives when the algebra
itself is projective over the base. The proof is the tensor-unit case
of the checked tensor-and-restriction splitting construction. -/

open _root_.CategoryTheory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBaseProjectives

set_option backward.isDefEq.respectTransparency false

universe u
variable (S A : Type u) [CommRing S] [CommRing A] [Algebra S A]

attribute [local instance] TensorOverBase.moduleCarrier
  TensorOverBase.scalarTowerCarrier

def tensorUnitIso : TensorOverBase.tensorOverBase S A (ModuleCat.of S S) ≅ 𝟭 (ModuleCat.{u} A) :=
  NatIso.ofComponents (fun M => (TensorProduct.AlgebraTensorModule.rid S A M).toModuleIso)
    (by
      intro M M' f
      apply ModuleCat.hom_ext
      apply TensorProduct.AlgebraTensorModule.ext
      intro m s
      exact (f.hom.map_smul_of_tower s m).symm)

def restrictedTensorUnitIso :
    TensorOverBaseProjectives.tensorRestriction S A S (ModuleCat.of S S) ≅ ModuleCat.restrictScalars (algebraMap S A) :=
  Functor.isoWhiskerRight (tensorUnitIso S A) (ModuleCat.restrictScalars (algebraMap S A)) ≪≫
    Functor.leftUnitor _

variable [Projective ((ModuleCat.restrictScalars (algebraMap S A)).obj (ModuleCat.of A A))]

instance restriction_preservesProjectiveObjects :
    (ModuleCat.restrictScalars.{u} (algebraMap S A)).PreservesProjectiveObjects where
  projective_obj {M} hM := by
    let : Projective ((TensorOverBaseProjectives.tensorRestriction S A S (ModuleCat.of S S)).obj (ModuleCat.of A A)) :=
      Projective.of_iso ((restrictedTensorUnitIso S A).app (ModuleCat.of A A)).symm inferInstance
    let : Projective M := hM
    let : (TensorOverBaseProjectives.tensorRestriction S A S (ModuleCat.of S S)).PreservesProjectiveObjects :=
      TensorOverBaseProjectives.tensorRestriction_preservesProjectiveObjects S A S (ModuleCat.of S S)
    exact Projective.of_iso ((restrictedTensorUnitIso S A).app M) inferInstance

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RestrictionProjectives
