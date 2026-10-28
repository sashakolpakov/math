import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Algebra.Category.Ring.Constructions

/-! # Model Cartesian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ModelCartesian

noncomputable section

/-! An algebra tensor-product model gives an actual Cartesian diagram of affine schemes. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C B] [Algebra R A]

theorem tensorModel_ring_isPushout (e : A ≃ₐ[R] R ⊗[C] B) :
    IsPushout (CommRingCat.ofHom (algebraMap C R)) (CommRingCat.ofHom (algebraMap C B))
      (CommRingCat.ofHom (algebraMap R A))
      (CommRingCat.ofHom (e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)) := by
  refine (CommRingCat.isPushout_tensorProduct C R B).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.symm.toRingEquiv.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp
  · ext r
    exact e.symm.commutes r
  · rfl

def tensorModelMap (e : A ≃ₐ[R] R ⊗[C] B) : Spec (.of A) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (e.symm.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom))

theorem tensorModelMap_isPullback (e : A ≃ₐ[R] R ⊗[C] B) :
    IsPullback (tensorModelMap e) (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap C B)))
      (Spec.map (CommRingCat.ofHom (algebraMap C R))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (tensorModel_ring_isPushout e)).flip

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ModelCartesian
