import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian.AffineGluing

/-! # Affine Gluing Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian

noncomputable section

/-! The glued morphism recovers the prescribed map on every noetherian affine test, including maps that are not open immersions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] (D : AffineGluing.NoetherianAffineMapData X Y)

theorem AffineGluing.NoetherianAffineMapData.glue_affine {R : CommRingCat.{u}} [IsNoetherianRing R] (x : Spec R ⟶ X) :
    x ≫ D.glue = D.map x := by
  let C := X.affineOpenCover
  let E : (Spec R).OpenCover := C.openCover.pullback₁ x
  apply E.hom_ext
  intro i
  change C.I₀ at i
  let : IsNoetherianRing (C.X i) := AffineGluing.affineCoverCoordinateRing_noetherian X i
  let W := pullback x (C.f i)
  have : IsOpenImmersion (pullback.fst x (C.f i)) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion)
      (IsPullback.of_hasPullback x (C.f i)).flip (C.openCover.map_prop i)
  have : IsLocallyNoetherian W := isLocallyNoetherian_of_isOpenImmersion (pullback.fst x (C.f i))
  apply W.affineOpenCover.openCover.hom_ext
  intro k
  let := AffineGluing.affineCoverCoordinateRing_noetherian W k
  let a := W.affineOpenCover.f k ≫ pullback.fst x (C.f i)
  let b := W.affineOpenCover.f k ≫ pullback.snd x (C.f i)
  have he : a ≫ x = b ≫ C.f i := by
    change (W.affineOpenCover.f k ≫ pullback.fst x (C.f i)) ≫ x =
      (W.affineOpenCover.f k ≫ pullback.snd x (C.f i)) ≫ C.f i
    rw [Category.assoc, Category.assoc, pullback.condition]
  have hc : C.f i ≫ D.glue = D.map (C.f i) := D.glue_chart i
  have h : (a ≫ x) ≫ D.glue = a ≫ D.map x := by
    rw [he, Category.assoc, hc, D.naturality, ← he, ← D.naturality]
  change W.affineOpenCover.f k ≫ (pullback.fst x (C.f i) ≫ (x ≫ D.glue)) =
    W.affineOpenCover.f k ≫ (pullback.fst x (C.f i) ≫ D.map x)
  exact (Category.assoc _ _ _).symm.trans
    ((Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _)))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Noetherian
