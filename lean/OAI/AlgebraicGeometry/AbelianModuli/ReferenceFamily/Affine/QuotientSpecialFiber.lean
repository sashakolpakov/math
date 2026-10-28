import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ModelCartesian
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Ideal.Over

/-! # Quotient Special Fiber -/

namespace OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.QuotientSpecialFiber

noncomputable section

/-! The quotient by an ideal extended from the base is the actual affine
scheme special fiber, with its literal quotient inclusion retained. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

theorem affine_quotient_specialFiber_isPullback
    (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (I : Ideal R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R S)))))
      (Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  have hm : e.symm.toRingHom.comp
      (Algebra.TensorProduct.includeRight : S →ₐ[R] (R ⧸ I) ⊗[R] S).toRingHom =
        Ideal.Quotient.mk (I.map (algebraMap R S)) := by
    apply RingHom.ext
    intro s
    apply e.injective
    change e (e.symm ((1 : R ⧸ I) ⊗ₜ[R] s)) = e (Ideal.Quotient.mk (I.map (algebraMap R S)) s)
    rw [e.apply_symm_apply, Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  have hmap : HilbertConstruction.Tensor.ModelCartesian.tensorModelMap e =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R S)))) := by
    change Spec.map (CommRingCat.ofHom _) = _
    rw [hm]
  have h := HilbertConstruction.Tensor.ModelCartesian.tensorModelMap_isPullback e
  rw [hmap] at h
  exact h

end

end OAI.AlgebraicGeometry.AbelianModuli.ReferenceFamily.Affine.QuotientSpecialFiber
