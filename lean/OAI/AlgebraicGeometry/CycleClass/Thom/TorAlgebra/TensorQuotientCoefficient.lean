import OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.DoubleTensorRepresentation
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Tensor Quotient Coefficient -/

namespace OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorQuotientCoefficient

noncomputable section

/-! For quotient modules the iterated tensor coefficient is the
quotient by the sum of the two extended ideals. All equivalences are
linear over the original algebra. -/

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open scoped TensorProduct

open OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorOverBase OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorModel
  TensorProjectionFormula DoubleTensorRepresentation

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

def freeQuotientIso (I : Ideal R) :
    (TensorOverBase.tensorOverBase R A (ModuleCat.of R (R ⧸ I))).obj (ModuleCat.of A A) ≅
      ModuleCat.of A (A ⧸ I.map (algebraMap R A)) :=
  ((TensorModel.tensorModelEquiv R A A (ModuleCat.of R (R ⧸ I))).trans
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.toLinearEquiv).toModuleIso

omit [Algebra R A] in
def tensorQuotientsIso (I J : Ideal A) :
    ModuleCat.of A ((A ⧸ I) ⊗[A] (A ⧸ J)) ≅ ModuleCat.of A (A ⧸ I ⊔ J) :=
  (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot (A ⧸ I) J).symm.toLinearEquiv.restrictScalars A).trans
    (DoubleQuot.quotQuotEquivQuotSupₐ A I J).toLinearEquiv).toModuleIso

variable (S : Type u) [CommRing S] [Algebra S A]

def coefficientQuotientIso (I : Ideal R) (J : Ideal S) :
    DoubleTensorRepresentation.coefficient S R A (ModuleCat.of S (S ⧸ J)) (ModuleCat.of R (R ⧸ I)) ≅
      ModuleCat.of A (A ⧸ J.map (algebraMap S A) ⊔ I.map (algebraMap R A)) :=
  (TensorOverBase.tensorOverBase R A (ModuleCat.of R (R ⧸ I))).mapIso (freeQuotientIso S A J) ≪≫
  (TensorProjectionFormula.tensorRepresentationIso R A (ModuleCat.of R (R ⧸ I))).app
    (ModuleCat.of A (A ⧸ J.map (algebraMap S A))) ≪≫
  (tensorLeft (ModuleCat.of A (A ⧸ J.map (algebraMap S A)))).mapIso (freeQuotientIso R A I) ≪≫
  tensorQuotientsIso A (J.map (algebraMap S A)) (I.map (algebraMap R A))

end

end OAI.AlgebraicGeometry.CycleClass.Thom.TorAlgebra.TensorQuotientCoefficient
