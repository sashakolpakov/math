import OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Tensor
import OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProjectionSmooth
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Product Square -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProductSquare.BundleCycles

noncomputable section

/-! Laurent polynomial extension is the actual product with the punctured affine line, by the tensor-product universal property. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

variable (A R : Type) [CommRing A] [CommRing R] [Algebra A R]

theorem laurentConstantSquare_isPushout :
    IsPushout (CommRingCat.ofHom (algebraMap A R))
      (CommRingCat.ofHom (algebraMap A (LaurentPolynomial A)))
      (CommRingCat.ofHom (algebraMap R (LaurentPolynomial R)))
      (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (algebraMap A R))) := by
  refine (CommRingCat.isPushout_tensorProduct A R (LaurentPolynomial A)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (AddMonoidAlgebra.scalarTensorEquiv A R (M := ℤ)).toCommRingCatIso
    (by simp) (by simp) ?_ ?_
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    exact (AddMonoidAlgebra.scalarTensorEquiv A R (M := ℤ)).commutes r
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro q
    change (AddMonoidAlgebra.scalarTensorEquiv A R (M := ℤ)) (1 ⊗ₜ[A] q) = _
    rw [AddMonoidAlgebra.scalarTensorEquiv_tmul, one_smul]
    rfl

theorem laurentProjection_isPullback :
    IsPullback (FiberGenericPoint.BundleCycles.laurentProjection R)
      (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom ℤ (algebraMap A R))))
      (Spec.map (CommRingCat.ofHom (algebraMap A R))) (FiberGenericPoint.BundleCycles.laurentProjection A) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (laurentConstantSquare_isPushout A R)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Laurent.ProductSquare.BundleCycles
