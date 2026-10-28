import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.CommonRecovery

/-! # Comparison Tensor Iso -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ComparisonTensorIso

noncomputable section

/-! The coordinate tensor map of two affine models with the same recovery is an isomorphism. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry TensorProduct

universe u

theorem affineOverMap_tensor_isIso_of_common_recovery
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {X Y : Over (Spec (.of C))} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    {P : Scheme.{u}} (p : P ⟶ Spec (.of R)) (qX : P ⟶ X.left) (qY : P ⟶ Y.left)
    (hX : IsPullback qX p X.hom (Spec.map (CommRingCat.ofHom (algebraMap C R))))
    (hY : IsPullback qY p Y.hom (Spec.map (CommRingCat.ofHom (algebraMap C R))))
    (hq : qX ≫ f.left = qY) :
    IsIso (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id R R) (OverMorphisms.affineOverMap C f)).toRingHom)) :=
  Tensor.ComparisonIso.isIso_naturalTensorMap_of_common_recovery (OverMorphisms.affineOverMap C f) p
    (qY ≫ (OverChartPoints.affineOverIso C Y).hom.left) (qX ≫ (OverChartPoints.affineOverIso C X).hom.left)
    (CommonRecovery.affineOver_common_recovery_isPullback Y qY p hY)
    (CommonRecovery.affineOver_common_recovery_isPullback X qX p hX)
    (CommonRecovery.affineOver_common_recovery_natural X f qX qY hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.ComparisonTensorIso
