import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.PushoutQuotientReduction
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Scalar Extension Fiber -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.ScalarExtensionFiber

noncomputable section

/-! Reducing the literal scalar extension gives the original fiber
tensor algebra. The constructed quotient equivalence retains both tensor
factors and the exact coefficient-reduction map. -/

open scoped TensorProduct

variable (R D k A : Type) [CommRing R] [CommRing D] [CommRing k] [CommRing A]
    [Algebra R D] [Algebra R k] [Algebra D k] [IsScalarTower R D k] [Algebra R A]

local instance tensorScalarFiber_sourceRing : CommRing (D ⊗[R] A) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := D) (B := A)

local instance tensorScalarFiber_targetRing : CommRing (k ⊗[R] A) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := A)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def tensorScalarExtensionReduction : (D ⊗[R] A) →ₐ[D] (k ⊗[R] A) :=
  Algebra.TensorProduct.map (Algebra.ofId D k) (AlgHom.id R A)

theorem tensorScalarExtensionReduction_tmul (d : D) (a : A) :
    tensorScalarExtensionReduction R D k A (d ⊗ₜ[R] a) = algebraMap D k d ⊗ₜ[R] a := rfl

@[instance_reducible]
def tensorScalarExtensionFiberAlgebra : Algebra (D ⊗[R] A) (k ⊗[R] A) :=
  (tensorScalarExtensionReduction R D k A).toRingHom.toAlgebra

attribute [local instance 50] tensorScalarExtensionFiberAlgebra

local instance tensorScalarFiber_baseTower : IsScalarTower D (D ⊗[R] A) (k ⊗[R] A) :=
  IsScalarTower.of_algebraMap_eq (fun d => ((tensorScalarExtensionReduction R D k A).commutes d).symm)

local instance tensorScalarFiber_originalTower : IsScalarTower A (D ⊗[R] A) (k ⊗[R] A) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  change (1 : k) ⊗ₜ[R] a = algebraMap D k 1 ⊗ₜ[R] a
  rw [map_one]

local instance tensorScalarFiber_groundTower : IsScalarTower R (D ⊗[R] A) (k ⊗[R] A) :=
  IsScalarTower.of_algebraMap_eq (fun r =>
    ((tensorScalarExtensionReduction R D k A).restrictScalars R).commutes r |>.symm)

theorem tensorScalarExtensionFiber_isPushout :
    Algebra.IsPushout D k (D ⊗[R] A) (k ⊗[R] A) :=
  PushoutQuotientReduction.scalarExtensionFiber_isPushout R D k A (D ⊗[R] A) (k ⊗[R] A)

def tensorScalarExtensionFiberQuotientEquiv (h : Function.Surjective (algebraMap D k)) :
    ((D ⊗[R] A) ⧸ (RingHom.ker (algebraMap D k)).map (algebraMap D (D ⊗[R] A))) ≃ₐ[D]
      (k ⊗[R] A) :=
  PushoutQuotientReduction.scalarExtensionFiberQuotientEquiv R D k A (D ⊗[R] A) (k ⊗[R] A) h

theorem tensorScalarExtensionFiberQuotientEquiv_mk
    (h : Function.Surjective (algebraMap D k)) (p : D ⊗[R] A) :
    tensorScalarExtensionFiberQuotientEquiv R D k A h
      (Ideal.Quotient.mk ((RingHom.ker (algebraMap D k)).map (algebraMap D (D ⊗[R] A))) p) =
        tensorScalarExtensionReduction R D k A p :=
  PushoutQuotientReduction.scalarExtensionFiberQuotientEquiv_mk R D k A (D ⊗[R] A) (k ⊗[R] A) h p

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.ScalarExtensionFiber
