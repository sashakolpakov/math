import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberTensorLifts
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentCoefficientProduct

/-! # Tangent Derivation Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentDerivationProduct

noncomputable section

/-! A coefficient derivation lifting a specified base tangent gives
an actual product equivalence with that exact second coefficient. -/

open scoped TensorProduct

variable (k R A : Type) [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra k A] [Algebra R k] [Algebra R A]
    [IsScalarTower k R k] [IsScalarTower k R A] [Algebra.FormallySmooth R A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (d : Derivation k R k) (l : Derivation k A (k ⊗[R] A))
    (hl : ∀ r, l (algebraMap R A r) = d r ⊗ₜ[R] (1 : A))

def tangentDerivationProductEquiv :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (DualNumber k ⊗[R] A) ≃ₐ[DualNumber k] (DualNumber k ⊗[k] (k ⊗[R] A)) :=
  TangentCoefficientProduct.tangentCoefficientProductEquiv k R A d (PointFiberTensorLifts.tangentDerivationLift k R A l)
    (PointFiberTensorLifts.tangentDerivationLift_reduction k R A l) (PointFiberTensorLifts.tangentDerivationLift_base k R A d l hl)

theorem tangentDerivationProductEquiv_snd (a : A) :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    (Dual.NumberCoefficients.dualTensorCoefficientEquiv k (k ⊗[R] A)
      (tangentDerivationProductEquiv k R A d l hl ((1 : DualNumber k) ⊗ₜ[R] a))).snd = l a :=
  (congrArg TrivSqZeroExt.snd (TangentCoefficientProduct.tangentCoefficientProductEquiv_coefficients k R A d
    (PointFiberTensorLifts.tangentDerivationLift k R A l) (PointFiberTensorLifts.tangentDerivationLift_reduction k R A l)
    (PointFiberTensorLifts.tangentDerivationLift_base k R A d l hl) a)).trans (PointFiberTensorLifts.tangentDerivationLift_snd k R A l a)

theorem tangentDerivationProductEquiv_reduction :
    letI qD := BaseTangentTensorLifts.baseTangentDualAlgebra k R d
    letI : Module R (DualNumber k) := qD.toModule
    letI : SMul R (DualNumber k) := qD.toSMul
    ∀ p, Dual.TensorReduction.dualTensorReduction k (k ⊗[R] A) (tangentDerivationProductEquiv k R A d l hl p) =
      BaseTangentTensor.baseTangentScalarReduction k R A d p :=
  TangentCoefficientProduct.tangentCoefficientProductEquiv_reduction k R A d (PointFiberTensorLifts.tangentDerivationLift k R A l)
    (PointFiberTensorLifts.tangentDerivationLift_reduction k R A l) (PointFiberTensorLifts.tangentDerivationLift_base k R A d l hl)

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.TangentDerivationProduct
