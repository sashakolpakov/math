import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.BaseTangentAffineLifts
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Point Fiber Tensor Lifts -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberTensorLifts

noncomputable section

section

/-! For an actual base point, the fiber tensor algebra carries the
original scalar actions. Every base tangent has a constructed linear
lift with coefficients in this fixed fiber algebra. -/

open scoped TensorProduct

variable (k R A : Type) [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra k A] [Algebra R k] [Algebra R A]
    [IsScalarTower k R k] [IsScalarTower k R A]

local instance pointFiberTensor_commRing : CommRing (k ⊗[R] A) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := A)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem pointFiberTensor_scalarTower : IsScalarTower k A (k ⊗[R] A) := by
  apply IsScalarTower.of_algebraMap_eq
  intro c
  rw [IsScalarTower.algebraMap_apply k R (k ⊗[R] A),
    IsScalarTower.algebraMap_apply k R A, IsScalarTower.algebraMap_apply R A (k ⊗[R] A)]

variable [Algebra.FormallySmooth R A]

def pointFiberTensorDerivation : Derivation k R k →ₗ[k] Derivation k A (k ⊗[R] A) := by
  have := pointFiberTensor_scalarTower k R A
  exact BaseTangentAffineLifts.baseTangentAffineDerivation k R A (k ⊗[R] A)

def pointFiberTensorLift (d : Derivation k R k) : A →ₐ[k] DualNumber (k ⊗[R] A) := by
  have := pointFiberTensor_scalarTower k R A
  exact BaseTangentAffineLifts.baseTangentAffineLift k R A (k ⊗[R] A) d

theorem pointFiberTensorLift_snd (d : Derivation k R k) (a : A) :
    (pointFiberTensorLift k R A d a).snd = pointFiberTensorDerivation k R A d a := by
  have := pointFiberTensor_scalarTower k R A
  exact BaseTangentAffineLifts.baseTangentAffineLift_snd k R A (k ⊗[R] A) d a

theorem pointFiberTensorLift_reduction (d : Derivation k R k) (a : A) :
    (pointFiberTensorLift k R A d a).fst = (1 : k) ⊗ₜ[R] a := by
  have := pointFiberTensor_scalarTower k R A
  exact BaseTangentAffineLifts.baseTangentAffineLift_reduction k R A (k ⊗[R] A) d a

theorem pointFiberTensorDerivation_base (d : Derivation k R k) (r : R) :
    pointFiberTensorDerivation k R A d (algebraMap R A r) = d r ⊗ₜ[R] (1 : A) := by
  have := pointFiberTensor_scalarTower k R A
  exact Smooth.CoefficientDerivationSection.smoothCoefficientDerivationSection_algebraMap k R A (k ⊗[R] A)
    (Dual.CoefficientLiftNaturality.coefficientDerivationMap k R k (k ⊗[R] A) (IsScalarTower.toAlgHom R k (k ⊗[R] A)) d) r

end

/-! A coefficient derivation with the prescribed base tangent gives
an actual affine dual-number lift with exactly that second coefficient
and the original fixed-fiber reduction. -/

open scoped TensorProduct

variable (k R A : Type) [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra k A] [Algebra R k] [Algebra R A]
    [IsScalarTower k R k] [IsScalarTower k R A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra pointFiberTensor_scalarTower

def tangentDerivationLift (l : Derivation k A (k ⊗[R] A)) : A →ₐ[k] DualNumber (k ⊗[R] A) :=
  ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k A (k ⊗[R] A)).symm l).val

theorem tangentDerivationLift_reduction (l : Derivation k A (k ⊗[R] A)) (a : A) :
    (tangentDerivationLift k R A l a).fst = (1 : k) ⊗ₜ[R] a :=
  AlgHom.congr_fun ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k A (k ⊗[R] A)).symm l).property a

theorem tangentDerivationLift_snd (l : Derivation k A (k ⊗[R] A)) (a : A) :
    (tangentDerivationLift k R A l a).snd = l a :=
  (Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv_apply k A (k ⊗[R] A) _ a).symm.trans
    (Derivation.congr_fun ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k A (k ⊗[R] A)).apply_symm_apply _) a)

theorem tangentDerivationLift_base (d : Derivation k R k) (l : Derivation k A (k ⊗[R] A))
    (hl : ∀ r, l (algebraMap R A r) = d r ⊗ₜ[R] (1 : A)) (r : R) :
    tangentDerivationLift k R A l (algebraMap R A r) =
      Dual.NumberCoefficients.dualNumberRingMap (algebraMap k (k ⊗[R] A))
        (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val r) := by
  apply TrivSqZeroExt.ext
  · have hd : (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val r).fst = algebraMap R k r :=
      AlgHom.congr_fun ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).property r
    change (tangentDerivationLift k R A l (algebraMap R A r)).fst =
      algebraMap k (k ⊗[R] A) (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val r).fst
    rw [tangentDerivationLift_reduction, hd]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := R) (A := k) (B := A) r).symm
  · have hd : (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val r).snd = d r :=
      (Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv_apply k R k _ r).symm.trans
        (Derivation.congr_fun ((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).apply_symm_apply _) r)
    change (tangentDerivationLift k R A l (algebraMap R A r)).snd =
      algebraMap k (k ⊗[R] A) (((Dual.AlgebraLiftCoordinates.dualAlgebraLiftDerivationEquiv k R k).symm d).val r).snd
    rw [tangentDerivationLift_snd, hl, hd]
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PointFiberTensorLifts
