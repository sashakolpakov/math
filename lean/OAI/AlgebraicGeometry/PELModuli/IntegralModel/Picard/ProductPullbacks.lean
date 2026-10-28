import OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductOpenCover

/-! # Product Pullbacks -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductPullbacks.PicardProductOpenCover

noncomputable section

/-! The actual product-family maps preserve cartesian parameter squares. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory

theorem productMap_preserves_isPullback {S : Scheme.{0}} (P : Over S) {W T U V : Over S}
    (a : W ⟶ T) (b : W ⟶ U) (f : T ⟶ V) (g : U ⟶ V) (H : IsPullback a b f g) :
    IsPullback (a ▷ P).left (b ▷ P).left (f ▷ P).left (g ▷ P).left := by
  let hbase := H.map (Over.forget S)
  let hrect := (ProductOpenCover.PicardProductOpenCover.productMap_isPullback P b).flip.paste_horiz hbase
  have ht : (fst W P).left ≫ a.left = (a ▷ P).left ≫ (fst T P).left :=
    (ProductOpenCover.PicardProductOpenCover.productMap_isPullback P a).w.symm
  have hb : (fst U P).left ≫ g.left = (g ▷ P).left ≫ (fst V P).left :=
    (ProductOpenCover.PicardProductOpenCover.productMap_isPullback P g).w.symm
  have hr : IsPullback ((a ▷ P).left ≫ (fst T P).left) (b ▷ P).left f.left
      ((g ▷ P).left ≫ (fst V P).left) :=
    (congrArg₂ (fun x y => IsPullback x (b ▷ P).left f.left y) ht hb).mp hrect
  have hc : (a ▷ P).left ≫ (f ▷ P).left = (b ▷ P).left ≫ (g ▷ P).left := by
    have h := congrArg Over.Hom.left (congrArg (· ▷ P) H.w)
    simpa only [comp_whiskerRight, Over.comp_left] using h
  exact IsPullback.of_right hr hc (ProductOpenCover.PicardProductOpenCover.productMap_isPullback P f).flip

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.Picard.ProductPullbacks.PicardProductOpenCover
