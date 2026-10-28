import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.ScalarExtensionFiber
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.ScalarExtensionMap
import OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.CommonFiberMapIsomorphism

/-! # Scalar Extension Product -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.ScalarExtensionProduct

noncomputable section

/-! A prescribed lift from the original affine algebra gives an
actual equivalence from its literal scalar extension to a smooth product.
The equivalence retains the chosen lift on every original function. -/

open scoped TensorProduct

variable (R D k A T : Type) [CommRing R] [CommRing D] [CommRing k] [CommRing A] [CommRing T]
    [Algebra R D] [Algebra R k] [Algebra D k] [IsScalarTower R D k] [Algebra R A]
    [Algebra R T] [Algebra D T] [IsScalarTower R D T] [Algebra.FormallySmooth D T]

local instance tensorScalarProduct_sourceRing : CommRing (D ⊗[R] A) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := D) (B := A)

local instance tensorScalarProduct_fiberRing : CommRing (k ⊗[R] A) :=
  Algebra.TensorProduct.instCommRing (R := R) (A := k) (B := A)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable (hD : Function.Surjective (algebraMap D k))
    (hI : RingHom.ker (algebraMap D k) * RingHom.ker (algebraMap D k) = ⊥)
    (eT : (T ⧸ (RingHom.ker (algebraMap D k)).map (algebraMap D T)) ≃ₐ[D] (k ⊗[R] A))
    (f : A →ₐ[R] T)
    (hf : ∀ a, eT (Ideal.Quotient.mk ((RingHom.ker (algebraMap D k)).map (algebraMap D T)) (f a)) =
      (1 : k) ⊗ₜ[R] a)

def tensorScalarExtensionProductEquiv : (D ⊗[R] A) ≃ₐ[D] T := by
  let eP := ScalarExtensionFiber.tensorScalarExtensionFiberQuotientEquiv R D k A hD
  let qT : T →ₐ[D] (k ⊗[R] A) :=
    eT.toAlgHom.comp (Ideal.Quotient.mkₐ D ((RingHom.ker (algebraMap D k)).map (algebraMap D T)))
  have H : qT.comp (Affine.ScalarExtensionMap.affineScalarExtensionMap R D A (D ⊗[R] A) T f) =
      ScalarExtensionFiber.tensorScalarExtensionReduction R D k A := by
    apply Affine.ScalarExtensionMap.affineScalarExtensionMap_reduction R D A (D ⊗[R] A) T (k ⊗[R] A)
    intro a
    change eT (Ideal.Quotient.mk _ (f a)) = algebraMap D k 1 ⊗ₜ[R] a
    rw [map_one]
    exact hf a
  apply CommonFiberMapIsomorphism.commonFiberMapEquiv (RingHom.ker (algebraMap D k)) hI eP eT
    (Affine.ScalarExtensionMap.affineScalarExtensionMap R D A (D ⊗[R] A) T f)
  intro p
  exact (AlgHom.congr_fun H p).trans (ScalarExtensionFiber.tensorScalarExtensionFiberQuotientEquiv_mk R D k A hD p).symm

theorem tensorScalarExtensionProductEquiv_toAlgHom :
    (tensorScalarExtensionProductEquiv R D k A T hD hI eT f hf).toAlgHom =
      Affine.ScalarExtensionMap.affineScalarExtensionMap R D A (D ⊗[R] A) T f := rfl

theorem tensorScalarExtensionProductEquiv_original (a : A) :
    tensorScalarExtensionProductEquiv R D k A T hD hI eT f hf ((1 : D) ⊗ₜ[R] a) = f a :=
  Affine.ScalarExtensionMap.affineScalarExtensionMap_algebraMap R D A (D ⊗[R] A) T f a

theorem tensorScalarExtensionProductEquiv_reduction (p : D ⊗[R] A) :
    eT (Ideal.Quotient.mk ((RingHom.ker (algebraMap D k)).map (algebraMap D T))
      (tensorScalarExtensionProductEquiv R D k A T hD hI eT f hf p)) =
        ScalarExtensionFiber.tensorScalarExtensionReduction R D k A p := by
  let qT : T →ₐ[D] (k ⊗[R] A) :=
    eT.toAlgHom.comp (Ideal.Quotient.mkₐ D ((RingHom.ker (algebraMap D k)).map (algebraMap D T)))
  have H : qT.comp (Affine.ScalarExtensionMap.affineScalarExtensionMap R D A (D ⊗[R] A) T f) =
      ScalarExtensionFiber.tensorScalarExtensionReduction R D k A := by
    apply Affine.ScalarExtensionMap.affineScalarExtensionMap_reduction R D A (D ⊗[R] A) T (k ⊗[R] A)
    intro a
    change eT (Ideal.Quotient.mk _ (f a)) = algebraMap D k 1 ⊗ₜ[R] a
    rw [map_one]
    exact hf a
  exact AlgHom.congr_fun H p

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Tensor.ScalarExtensionProduct
