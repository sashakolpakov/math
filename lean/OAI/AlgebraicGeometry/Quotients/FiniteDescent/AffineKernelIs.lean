import OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineRing
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affine Kernel Is -/

namespace OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineKernelIs.Construction.AffineKernel

/-!
# The affine quotient kernel pair

A tensor equivalence respecting source and target identifies the given
affine relation with the scheme-theoretic kernel pair of the quotient map.
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open scoped TensorProduct

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A compatible tensor-square equivalence exhibits the invariant inclusion
square as a pushout of commutative rings. -/
theorem isPushout_of_tensor_equiv (t : A →+* B)
    (e : let C := (algebraMap A B).eqLocus t
      letI : Algebra C A := C.subtype.toAlgebra
      A ⊗[C] A ≃ₐ[A] B)
    (he : let C := (algebraMap A B).eqLocus t
      letI : Algebra C A := C.subtype.toAlgebra
      ∀ a a', e (a ⊗ₜ[C] a') = algebraMap A B a * t a') :
    IsPushout (CommRingCat.ofHom ((algebraMap A B).eqLocus t).subtype)
      (CommRingCat.ofHom ((algebraMap A B).eqLocus t).subtype)
      (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom t) := by
  let C := (algebraMap A B).eqLocus t
  let : Algebra C A := C.subtype.toAlgebra
  refine (CommRingCat.isPushout_tensorProduct C A A).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso (by simp) (by simp) ?_ ?_
  · ext a
    change e (a ⊗ₜ[C] 1) = algebraMap A B a
    simpa only [map_one, mul_one] using he a 1
  · ext a
    change e (1 ⊗ₜ[C] a) = t a
    simpa only [map_one, one_mul] using he 1 a

/-- Taking spectra turns the compatible invariant tensor square into the
actual scheme-theoretic kernel pair of the affine quotient projection. -/
theorem projection_isKernelPair_of_tensor_equiv (t : A →+* B)
    (e : let C := (algebraMap A B).eqLocus t
      letI : Algebra C A := C.subtype.toAlgebra
      A ⊗[C] A ≃ₐ[A] B)
    (he : let C := (algebraMap A B).eqLocus t
      letI : Algebra C A := C.subtype.toAlgebra
      ∀ a a', e (a ⊗ₜ[C] a') = algebraMap A B a * t a') :
    IsKernelPair (AffineRing.Construction.Affine.projection (algebraMap A B) t)
      (Spec.map (CommRingCat.ofHom (algebraMap A B))) (Spec.map (CommRingCat.ofHom t)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_of_tensor_equiv t e he)

end OAI.AlgebraicGeometry.Quotients.FiniteDescent.AffineKernelIs.Construction.AffineKernel
