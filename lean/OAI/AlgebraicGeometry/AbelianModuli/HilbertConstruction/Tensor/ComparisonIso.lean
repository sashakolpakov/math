import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.ChangedComparisonIso
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.NaturalTensorMapCartesian

/-! # Comparison Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonIso

noncomputable section

/-! A comparison of affine models with common scheme recovery becomes a tensor-product isomorphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u

variable {C R A B : Type u} [CommRing C] [CommRing R] [CommRing A] [CommRing B]
variable [Algebra C R] [Algebra C A] [Algebra C B]

theorem naturalTensorProjection_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := C) (A := R) (B := A)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[C] A))))
      (Spec.map (CommRingCat.ofHom (algebraMap C A)))
      (Spec.map (CommRingCat.ofHom (algebraMap C R))) :=
  ModelCartesian.tensorModelMap_isPullback (AlgEquiv.refl : R ⊗[C] A ≃ₐ[R] R ⊗[C] A)

theorem algebraSpecMap_over (φ : A →ₐ[C] B) :
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap C A)) =
      Spec.map (CommRingCat.ofHom (algebraMap C B)) := by
  rw [← Spec.map_comp]
  congr 1
  ext c
  exact φ.commutes c

theorem isIso_naturalTensorMap_of_common_recovery (φ : A →ₐ[C] B)
    {P : Scheme.{u}} (p : P ⟶ Spec (.of R))
    (qA : P ⟶ Spec (.of A)) (qB : P ⟶ Spec (.of B))
    (hA : IsPullback qA p (Spec.map (CommRingCat.ofHom (algebraMap C A)))
      (Spec.map (CommRingCat.ofHom (algebraMap C R))))
    (hB : IsPullback qB p (Spec.map (CommRingCat.ofHom (algebraMap C B)))
      (Spec.map (CommRingCat.ofHom (algebraMap C R))))
    (hq : qB ≫ Spec.map (CommRingCat.ofHom φ.toRingHom) = qA) :
    IsIso (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom)) := by
  exact Base.ChangedComparisonIso.isIso_baseChanged_comparison_of_common_recovery
    qB qA p _ _ _ (Spec.map (CommRingCat.ofHom φ.toRingHom)) (algebraSpecMap_over φ)
    hB hA hq _ _ _ _
    (naturalTensorProjection_isPullback (C := C) (R := R) (A := B))
    (naturalTensorProjection_isPullback (C := C) (R := R) (A := A))
    (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id R R) φ).toRingHom))
    (NaturalTensorMapCartesian.naturalTensorMap_isPullback (R := R) φ).w
    (algebraSpecMap_over (Algebra.TensorProduct.map (AlgHom.id R R) φ))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.ComparisonIso
