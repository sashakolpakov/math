import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorProjectives
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RightRestrictionProjectives
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorRestrictionSquare
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ResolutionViaProjectiveRestriction

/-! # External Tensor Resolution -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorResolution

noncomputable section

/-! A projective resolution over the tensor algebra becomes a
projective resolution over the left ring after tensoring over the right
ring, when the resolved object is projective over that right ring. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorProjectives OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.RightRestrictionProjectives

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (k R S : Type u) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
  (N : ModuleCat.{u} S) (X : ModuleCat.{u} (R ⊗[k] S))
  [Projective ((RightRestrictionProjectives.rightRestriction k R S).obj X)]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def resolution (P : ProjectiveResolution X) :
    ProjectiveResolution ((ExternalTensorProjectives.externalTensor k R S N).obj X) := by
  let F := ExternalTensorProjectives.externalTensor k R S N
  let F' := tensorRight N ⋙ ModuleCat.restrictScalars (algebraMap k S)
  let H := RightRestrictionProjectives.rightRestriction k R S
  let G := ModuleCat.restrictScalars (algebraMap k R)
  let : H.Additive := by dsimp [H, RightRestrictionProjectives.rightRestriction]; infer_instance
  let : H.PreservesHomology := by dsimp [H, RightRestrictionProjectives.rightRestriction]; infer_instance
  let : F.Additive := by
    dsimp [F, ExternalTensorProjectives.externalTensor, TensorOverBaseProjectives.tensorRestriction]
    infer_instance
  let : PreservesFiniteColimits F := by
    let : PreservesFiniteColimits (TensorOverBase.tensorOverBase S (R ⊗[k] S) N) :=
      TensorOverBase.tensorOverBase_preservesFiniteColimits S (R ⊗[k] S) N
    let : PreservesFiniteColimits (ModuleCat.restrictScalars.{u} (algebraMap R (R ⊗[k] S))) :=
      inferInstance
    change PreservesFiniteColimits (TensorOverBase.tensorOverBase S (R ⊗[k] S) N ⋙
      ModuleCat.restrictScalars (algebraMap R (R ⊗[k] S)))
    exact comp_preservesFiniteColimits _ _
  exact ResolutionViaProjectiveRestriction.resolution F F' H G
    (TensorRestrictionSquare.tensorRestrictionSquare k R S (R ⊗[k] S) N) X P

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorResolution
