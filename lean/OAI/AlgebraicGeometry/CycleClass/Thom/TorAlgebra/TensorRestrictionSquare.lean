import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBaseProjectives

/-! # Tensor Restriction Square -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorRestrictionSquare

noncomputable section

/-! The two base-scalar forgetful paths identify tensoring over the
right ring with the native right tensor functor. This is an actual
natural isomorphism of functors, including both algebra actions. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBaseProjectives

universe u
variable (k R S A : Type u) [CommRing k] [CommRing R] [CommRing S] [CommRing A]
  [Algebra k R] [Algebra k S] [Algebra k A] [Algebra R A] [Algebra S A]
  [IsScalarTower k R A] [IsScalarTower k S A] (N : ModuleCat.{u} S)

def baseRestrictionIso :
    ModuleCat.restrictScalars (algebraMap S A) ⋙ ModuleCat.restrictScalars (algebraMap k S) ≅
      ModuleCat.restrictScalars (algebraMap R A) ⋙ ModuleCat.restrictScalars (algebraMap k R) :=
  (ModuleCat.restrictScalarsComp' (algebraMap k S) (algebraMap S A) (algebraMap k A)
    (IsScalarTower.algebraMap_eq k S A)).symm ≪≫
  ModuleCat.restrictScalarsComp' (algebraMap k R) (algebraMap R A) (algebraMap k A)
    (IsScalarTower.algebraMap_eq k R A)

def tensorRestrictionSquare :
    ModuleCat.restrictScalars (algebraMap S A) ⋙
        (tensorRight N ⋙ ModuleCat.restrictScalars (algebraMap k S)) ≅
      TensorOverBaseProjectives.tensorRestriction S A R N ⋙ ModuleCat.restrictScalars (algebraMap k R) :=
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight (TensorOverBase.underlyingIso S A N).symm
    (ModuleCat.restrictScalars (algebraMap k S)) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (TensorOverBase.tensorOverBase S A N) (baseRestrictionIso k R S A) ≪≫
  (Functor.associator _ _ _).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorRestrictionSquare
