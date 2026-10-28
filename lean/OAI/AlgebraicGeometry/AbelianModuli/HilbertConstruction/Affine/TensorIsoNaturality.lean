import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorOverIso

/-! # Tensor Iso Naturality -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorIsoNaturality

noncomputable section

/-! The affine tensor presentation isomorphisms commute with every base-changed morphism. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u

theorem affineTensorOverIso_natural
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {X Y : Over (Spec (.of C))} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    TensorOverIso.affineTensorOverMap C R f ≫ (TensorOverIso.affineTensorOverIso C R Y).hom =
      (TensorOverIso.affineTensorOverIso C R X).hom ≫
        (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map f := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap C R))
  let t : (TensorOverIso.affineTensorOver C R X).left ⟶ (TensorOverIso.affineTensorOver C R Y).left :=
    (TensorOverIso.affineTensorOverMap C R f).left
  let eX : (TensorOverIso.affineTensorOver C R X).left ⟶ pullback X.hom c := (TensorOverIso.affineTensorOverIso C R X).hom.left
  let eY : (TensorOverIso.affineTensorOver C R Y).left ⟶ pullback Y.hom c := (TensorOverIso.affineTensorOverIso C R Y).hom.left
  let fR : pullback X.hom c ⟶ pullback Y.hom c := ((Over.pullback c).map f).left
  have heX : eX ≫ pullback.fst X.hom c = TensorProjection.affineTensorProjection C R X := TensorOverIso.affineTensorOverIso_hom_fst C R X
  have heY : eY ≫ pullback.fst Y.hom c = TensorProjection.affineTensorProjection C R Y := TensorOverIso.affineTensorOverIso_hom_fst C R Y
  have hfR : fR ≫ pullback.fst Y.hom c = pullback.fst X.hom c ≫ f.left := pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  change t ≫ eY = eX ≫ fR
  apply pullback.hom_ext
  · rw [Category.assoc, heY, Category.assoc, hfR, ← Category.assoc, heX]
    exact TensorProjectionNaturality.affineTensorProjection_natural R f
  · exact ((TensorOverIso.affineTensorOverMap C R f) ≫ (TensorOverIso.affineTensorOverIso C R Y).hom).w.trans
      (((TensorOverIso.affineTensorOverIso C R X).hom ≫ (Over.pullback c).map f).w).symm

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TensorIsoNaturality
