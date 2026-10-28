import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ModelCartesian
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-! # Natural Tensor Map Cartesian -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapCartesian

noncomputable section

/-! The natural tensor extension of an affine morphism is its actual base change. -/

open TensorProduct _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

theorem naturalTensorMap_ring_isPushout (φ : A →ₐ[C] B) :
    IsPushout (CommRingCat.ofHom φ.toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := C) (A := R) (B := A)).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := C) (A := R) (B := B)).toRingHom)
      (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom) := by
  let m := CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom
  have htop : CommRingCat.ofHom (algebraMap C A) ≫ CommRingCat.ofHom φ.toRingHom =
      CommRingCat.ofHom (algebraMap C B) := by
    ext c
    exact φ.commutes c
  have hbot : CommRingCat.ofHom (algebraMap R (R ⊗[C] A)) ≫ m =
      CommRingCat.ofHom (algebraMap R (R ⊗[C] B)) := by
    ext r
    exact (Algebra.TensorProduct.map (AlgHom.id R R) φ).commutes r
  have hbig : IsPushout
      (CommRingCat.ofHom (algebraMap C A) ≫ CommRingCat.ofHom φ.toRingHom)
      (CommRingCat.ofHom (algebraMap C R))
      (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := C) (A := R) (B := B)).toRingHom)
      (CommRingCat.ofHom (algebraMap R (R ⊗[C] A)) ≫ m) := by
    rw [htop, hbot]
    exact (CommRingCat.isPushout_tensorProduct C R B).flip
  apply hbig.of_left ?_ (CommRingCat.isPushout_tensorProduct C R A).flip
  ext a
  change (1 : R) ⊗ₜ[C] φ a = Algebra.TensorProduct.map (AlgHom.id R R) φ ((1 : R) ⊗ₜ[C] a)
  exact (Algebra.TensorProduct.map_tmul (AlgHom.id R R) φ (1 : R) a).symm

theorem naturalTensorMap_isPullback (φ : A →ₐ[C] B) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := C) (A := R) (B := B)).toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := C) (A := R) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom φ.toRingHom)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (naturalTensorMap_ring_isPushout (R := R) φ)).flip

theorem natural_tensorMap_isOpenImmersion (φ : A →ₐ[C] B)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom φ.toRingHom))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom)) :=
  MorphismProperty.of_isPullback (naturalTensorMap_isPullback (R := R) φ).flip inferInstance

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapCartesian
