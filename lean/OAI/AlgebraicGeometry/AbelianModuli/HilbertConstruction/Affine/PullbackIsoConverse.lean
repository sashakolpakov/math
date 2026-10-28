import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackIso

/-! # Pullback Iso Converse -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackIsoConverse

noncomputable section

/-! An actual affine base-change isomorphism gives a bijective coordinate tensor map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry TensorProduct

universe u

theorem affine_tensor_bijective_of_pullback_isIso
    {C R : Type u} [CommRing C] [CommRing R] [Algebra C R]
    {X Y : Over (Spec (.of C))} [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y)
    [IsIso ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap C R)))).map f)] :
    Function.Bijective (Algebra.TensorProduct.map (AlgHom.id R R) (OverMorphisms.affineOverMap C f)) := by
  let c := Spec.map (CommRingCat.ofHom (algebraMap C R))
  let g := (Over.pullback c).map f
  have : IsIso g.left := (Over.forget _).map_isIso g
  have hY : IsPullback (g.left ≫ pullback.fst Y.hom c) (pullback.snd X.hom c) Y.hom c := by
    apply (IsPullback.of_hasPullback Y.hom c).of_iso' (asIso g.left)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · change g.left ≫ pullback.snd Y.hom c = pullback.snd X.hom c
      exact g.w
    · simp
    · simp
  have hq : pullback.fst X.hom c ≫ f.left = g.left ≫ pullback.fst Y.hom c := by
    change _ = pullback.lift _ _ _ ≫ pullback.fst _ _
    exact (pullback.lift_fst _ _ _).symm
  exact isIso_SpecMap_iff.mp (ComparisonTensorIso.affineOverMap_tensor_isIso_of_common_recovery f
    (pullback.snd X.hom c) (pullback.fst X.hom c) (g.left ≫ pullback.fst Y.hom c)
    (IsPullback.of_hasPullback X.hom c) hY hq)

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackIsoConverse
