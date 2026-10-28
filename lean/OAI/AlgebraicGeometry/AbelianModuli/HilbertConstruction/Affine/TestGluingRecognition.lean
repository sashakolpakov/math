import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.TestGluing

/-! # Test Gluing Recognition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine

noncomputable section

/-! The glued morphism recovers the prescribed map on every affine test, including maps that are not open immersions. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (D : TestGluing.AffineTestMapData X Y)

theorem TestGluing.AffineTestMapData.glue_affine {R : CommRingCat.{u}} (x : Spec R ⟶ X) :
    x ≫ D.glue = D.map x := by
  let C := X.affineOpenCover
  let E : (Spec R).OpenCover := C.openCover.pullback₁ x
  apply E.hom_ext
  intro i
  change C.I₀ at i
  let W := pullback x (C.f i)
  apply W.affineOpenCover.openCover.hom_ext
  intro k
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

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine
