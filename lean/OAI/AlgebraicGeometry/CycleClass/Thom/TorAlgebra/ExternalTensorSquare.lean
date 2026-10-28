import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DoubleTensorRepresentation
import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorProjectives
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-! # External Tensor Square -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorSquare

noncomputable section

/-! The two embeddings in the tensor algebra are fixed before the
two scalar rings are specialized to the same ring. The comparison uses
the actual iterated tensor module as its algebra coefficient. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DoubleTensorRepresentation OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorProjectives

universe u
variable (k R S : Type u) [Field k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
  (N : ModuleCat.{u} S) (M : ModuleCat.{u} R)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def externalCoefficient : ModuleCat.{u} (R ⊗[k] S) :=
  DoubleTensorRepresentation.coefficient S R (R ⊗[k] S) N M

def externalTensorSquare :
    tensorLeft (externalCoefficient k R S N M) ⋙
        ModuleCat.restrictScalars (algebraMap R (R ⊗[k] S)) ≅
      ExternalTensorProjectives.externalTensor k R S N ⋙ tensorLeft M :=
  Functor.isoWhiskerRight (BraidedCategory.tensorLeftIsoTensorRight (externalCoefficient k R S N M))
    (ModuleCat.restrictScalars (algebraMap R (R ⊗[k] S))) ≪≫
  DoubleTensorRepresentation.underlyingDoubleTensorIso S R (R ⊗[k] S) N M ≪≫
  Functor.isoWhiskerLeft (ExternalTensorProjectives.externalTensor k R S N) (BraidedCategory.tensorLeftIsoTensorRight M).symm

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.ExternalTensorSquare
