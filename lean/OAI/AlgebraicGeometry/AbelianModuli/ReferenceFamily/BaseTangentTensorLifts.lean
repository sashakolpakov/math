import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentAffineLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Dual.CoefficientLiftTensorMap

/-! # Base Tangent Tensor Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentTensorLifts

noncomputable section

/-! The base tangent vector itself determines the dual-number base
algebra and an actual affine lift into the constant tensor product. The
second coefficient remains linear in that original tangent vector. -/

open scoped TensorProduct

variable (k R S B : Type) [Field k] [CommRing R] [CommRing S] [CommRing B]
    [Algebra k R] [Algebra k S] [Algebra k B] [Algebra R S] [Algebra R k] [Algebra R B] [Algebra S B]
    [IsScalarTower k R S] [IsScalarTower k R k] [IsScalarTower k R B] [IsScalarTower k S B]
    [IsScalarTower R k B] [IsScalarTower R S B] [Algebra.FormallySmooth R S]

local instance baseTangentTensor_commRing : CommRing (DualNumber k ⊗[k] B) :=
  Algebra.TensorProduct.instCommRing (R := k) (A := DualNumber k) (B := B)

@[instance_reducible]
def baseTangentDualAlgebra (d : Derivation k R k) : Algebra R (DualNumber k) :=
  ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val.toRingHom.toAlgebra

@[instance_reducible]
def baseTangentProductAlgebra (d : Derivation k R k) : Algebra R (DualNumber k ⊗[k] B) :=
  ((algebraMap (DualNumber k) (DualNumber k ⊗[k] B)).comp
    ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val.toRingHom).toAlgebra

def baseTangentTensorLift (d : Derivation k R k) :
    letI := baseTangentProductAlgebra k R B d
    S →ₐ[R] (DualNumber k ⊗[k] B) := by
  let := baseTangentDualAlgebra k R d
  let := baseTangentProductAlgebra k R B d
  exact Dual.CoefficientLiftTensorMap.dualCoefficientLiftTensorMap k R S B (fun _ => rfl) (BaseTangentAffineLifts.baseTangentAffineLift k R S B d)
    (BaseTangentAffineLifts.baseTangentAffineLift_base k R S B d)

theorem baseTangentTensorLift_coefficients (d : Derivation k R k) (s : S) :
    Dual.NumberCoefficients.dualTensorCoefficientEquiv k B (baseTangentTensorLift k R S B d s) = BaseTangentAffineLifts.baseTangentAffineLift k R S B d s := by
  let := baseTangentDualAlgebra k R d
  let := baseTangentProductAlgebra k R B d
  exact Dual.CoefficientLiftTensorMap.dualCoefficientLiftTensorMap_coefficients k R S B (fun _ => rfl)
    (BaseTangentAffineLifts.baseTangentAffineLift k R S B d) (BaseTangentAffineLifts.baseTangentAffineLift_base k R S B d) s

theorem baseTangentTensorLift_reduction (d : Derivation k R k) (s : S) :
    Dual.TensorReduction.dualTensorReduction k B (baseTangentTensorLift k R S B d s) = algebraMap S B s :=
  (congrArg TrivSqZeroExt.fst (baseTangentTensorLift_coefficients k R S B d s)).trans
    (BaseTangentAffineLifts.baseTangentAffineLift_reduction k R S B d s)

theorem baseTangentTensorLift_snd (d : Derivation k R k) (s : S) :
    (Dual.NumberCoefficients.dualTensorCoefficientEquiv k B (baseTangentTensorLift k R S B d s)).snd =
      BaseTangentAffineLifts.baseTangentAffineDerivation k R S B d s :=
  (congrArg TrivSqZeroExt.snd (baseTangentTensorLift_coefficients k R S B d s)).trans
    (BaseTangentAffineLifts.baseTangentAffineLift_snd k R S B d s)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentTensorLifts
