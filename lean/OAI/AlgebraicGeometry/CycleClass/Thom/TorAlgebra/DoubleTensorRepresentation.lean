import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorProjectionFormula

/-! # Double Tensor Representation -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DoubleTensorRepresentation

noncomputable section

/-! Iterated tensoring over the two scalar rings is represented by
tensoring over the algebra with its value on the free rank-one module.
Restriction to the final scalar ring identifies the same functor with
the ordinary tensor functor applied after the first scalar restriction. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBaseProjectives
  TensorProjectionFormula

universe u
variable (S R A : Type u) [CommRing S] [CommRing R] [CommRing A] [Algebra S A] [Algebra R A]
  (N : ModuleCat.{u} S) (M : ModuleCat.{u} R)

def coefficient : ModuleCat.{u} A :=
  (TensorOverBase.tensorOverBase R A M).obj ((TensorOverBase.tensorOverBase S A N).obj (ModuleCat.of A A))

def doubleRepresentationIso :
    TensorOverBase.tensorOverBase S A N ⋙ TensorOverBase.tensorOverBase R A M ≅ tensorRight (coefficient S R A N M) :=
  Functor.isoWhiskerRight (TensorProjectionFormula.tensorRepresentationIso S A N) (TensorOverBase.tensorOverBase R A M) ≪≫
  TensorProjectionFormula.tensorAssocIso R A M ((TensorOverBase.tensorOverBase S A N).obj (ModuleCat.of A A))

def underlyingDoubleTensorIso :
    tensorRight (coefficient S R A N M) ⋙ ModuleCat.restrictScalars (algebraMap R A) ≅
      TensorOverBaseProjectives.tensorRestriction S A R N ⋙ tensorRight M :=
  Functor.isoWhiskerRight (doubleRepresentationIso S R A N M).symm
    (ModuleCat.restrictScalars (algebraMap R A)) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (TensorOverBase.tensorOverBase S A N) (TensorOverBase.underlyingIso R A M) ≪≫
  (Functor.associator _ _ _).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DoubleTensorRepresentation
