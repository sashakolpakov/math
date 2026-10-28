import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.RingTheory.TensorProduct.Quotient

/-! # Quotient Pushout -/

namespace OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPushout.Construction

noncomputable section

/-! Quotient-ring pushouts, with the actual quotient and structure maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped TensorProduct

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (I : Ideal R)

/-- Extending an ideal is the pushout of its quotient map. -/
theorem quotient_isPushout :
    IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk I))
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f)))
      (CommRingCat.ofHom (Ideal.quotientMap (I.map f) f (Ideal.le_comap_map))) := by
  let : Algebra R S := f.toAlgebra
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toRingEquiv.toCommRingCatIso
  apply (CommRingCat.isPushout_tensorProduct R S (R ⧸ I)).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm
  · rfl
  · rfl
  · ext x
    exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm_apply_eq.mpr rfl
  · ext x
    apply (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).injective
    simp [e]
    change (f x * 1) ⊗ₜ[R] 1 = f x ⊗ₜ[R] 1
    rw [mul_one]

/-- Any actual pushout square against a quotient has the same quotient target. -/
def quotientPushoutIso {T : CommRingCat.{u}}
    {a : CommRingCat.of S ⟶ T} {b : CommRingCat.of (R ⧸ I) ⟶ T}
    (h : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk I)) a b) :
    CommRingCat.of (S ⧸ I.map f) ≅ T :=
  (quotient_isPushout f I).isoIsPushout _ _ h

theorem quotientPushoutIso_mk {T : CommRingCat.{u}}
    {a : CommRingCat.of S ⟶ T} {b : CommRingCat.of (R ⧸ I) ⟶ T}
    (h : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk I)) a b)
    (s : S) : (quotientPushoutIso f I h).hom (Ideal.Quotient.mk (I.map f) s) = a s := by
  exact ConcreteCategory.congr_hom ((quotient_isPushout f I).inl_isoIsPushout_hom _ _ h) s

end

end OAI.AlgebraicGeometry.FormalGeometry.Completion.QuotientPushout.Construction
