import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Quotient Base Change -/

namespace OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientBaseChange.Construction

noncomputable section

/-! Actual affine base change of closed centers and their kernel ideal sheaves. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The quotient by the extended ideal is the actual scheme pullback of
the original closed affine center. -/
theorem affineQuotient_baseChange_isPullback (I : Ideal R) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R S)))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      (Spec.map (CommRingCat.ofHom (algebraMap R S))) := by
  let e := Algebra.TensorProduct.quotIdealMapEquivQuotTensor S I
  apply isPullback_SpecMap_of_isPushout
  apply (CommRingCat.isPushout_tensorProduct R (R ⧸ I) S).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm.toRingEquiv.toCommRingCatIso
  · simp
  · simp
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    exact e.symm.commutes x
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    change e.symm (1 ⊗ₜ[R] x) = Ideal.Quotient.mk (I.map (algebraMap R S)) x
    apply e.injective
    rw [e.apply_symm_apply]
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk S I x).symm

/-- Pullback of the actual affine center kernel is precisely the kernel
of the quotient by the extended ideal. -/
theorem affineQuotient_kernel_comap (I : Ideal R) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap R S))))).ker := by
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hpb := (affineQuotient_baseChange_isPullback (S := S) I).flip
  have h := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S)))
  rw [← hpb.isoPullback_inv_fst, Scheme.Hom.ker_comp_of_isIso] at h
  exact h.symm

end

end OAI.AlgebraicGeometry.Resolution.Blowups.Affine.QuotientBaseChange.Construction
