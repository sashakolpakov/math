import OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Biextension.Compatibility

/-! # Interchange Neutral Frames -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.InterchangeNeutralFrames

noncomputable section

/-!
# Biextension interchange forces transverse multiplication of normalized neutral frames

The transverse product of two unit frames is an invertible idempotent for the other product.
Its unit-valued ratio with the normalized unit is therefore one. No transverse normalization
is assumed in this argument.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u

open OAI.AlgebraicGeometry.Picard.PoincareBundle.Line.Fibers OAI.AlgebraicGeometry.Picard.PoincareBundle.FiberwiseMultiplication OAI.AlgebraicGeometry.Picard.PoincareBundle.Bilinear.ProductFrames

variable {S : Scheme.{u}} {A X : Over S} [GrpObj A] [GrpObj X]
  (L : Line.Bundles.LineBundle (A ⊗ X).left)
  (Dh : FiberwiseMultiplication.Multiplication (fst A X) (snd A X) L) (Dv : FiberwiseMultiplication.Multiplication (snd A X) (fst A X) L)
  (hi : Biextension.Compatibility.Interchange L Dh Dv)

/-- A point neutral in one coordinate is idempotent in that coordinate. -/
theorem neutral_rel {E G K T : Over S} [GrpObj G] (p : E ⟶ G) (r : E ⟶ K)
    (a : T ⟶ E) (ha : a ≫ p = 1) : FiberwiseMultiplication.ProductRel p r a a a :=
  ⟨by rw [ha, one_mul], rfl, rfl⟩

include hi in
/-- Horizontal neutral frames multiply correctly under the actual vertical product. -/
theorem horizontal_units_vertical_product {T : Over S} (a b c : T ⟶ A ⊗ X)
    (ha : a ≫ fst A X = 1) (hb : b ≫ fst A X = 1) (hc : c ≫ fst A X = 1)
    (h : FiberwiseMultiplication.ProductRel (snd A X) (fst A X) a b c) (U : T.left.Opens) :
    (Dv.product a b c h).app U ((Dh.unitFrame a ha).hom.app U (1 : Γ(T.left, U)))
      ((Dh.unitFrame b hb).hom.app U (1 : Γ(T.left, U))) =
      (Dh.unitFrame c hc).hom.app U (1 : Γ(T.left, U)) := by
  let haa := neutral_rel (fst A X) (snd A X) a ha
  let hbb := neutral_rel (fst A X) (snd A X) b hb
  let hcc := neutral_rel (fst A X) (snd A X) c hc
  have : IsIso (Bilinear.BilinearPullback.toHom (Dv.product a b c h)) := Dv.product_isIso a b c h
  let s := Bilinear.ProductFrames.productFrame (Dv.product a b c h) (Dh.unitFrame a ha) (Dh.unitFrame b hb)
  have hs : (Dh.product c c c hcc).app ⊤ (s.hom.app ⊤ (1 : Γ(T.left, ⊤)))
      (s.hom.app ⊤ (1 : Γ(T.left, ⊤))) = s.hom.app ⊤ (1 : Γ(T.left, ⊤)) := by
    have hh := hi T a b a b c a b c c hbb h haa h h hcc ⊤
      ((Dh.unitFrame a ha).hom.app ⊤ (1 : Γ(T.left, ⊤)))
      ((Dh.unitFrame b hb).hom.app ⊤ (1 : Γ(T.left, ⊤)))
      ((Dh.unitFrame a ha).hom.app ⊤ (1 : Γ(T.left, ⊤)))
      ((Dh.unitFrame b hb).hom.app ⊤ (1 : Γ(T.left, ⊤)))
    rw [Dh.unit_left a a ha haa, Dh.unit_left b b hb hbb] at hh
    change (Dh.product c c c hcc).app ⊤
      ((Bilinear.ProductFrames.productFrame (Dv.product a b c h) (Dh.unitFrame a ha) (Dh.unitFrame b hb)).hom.app ⊤ (1 : Γ(T.left, ⊤)))
      ((Bilinear.ProductFrames.productFrame (Dv.product a b c h) (Dh.unitFrame a ha) (Dh.unitFrame b hb)).hom.app ⊤ (1 : Γ(T.left, ⊤))) = _
    rw [Bilinear.ProductFrames.productFrame_app]
    exact hh.symm
  have he : s = Dh.unitFrame c hc := Bilinear.ProductFrames.idempotent_frame_unique (Dh.product c c c hcc) s
    (Dh.unitFrame c hc) hs (Dh.unit_left c c hc hcc ⊤ _)
  exact (Bilinear.ProductFrames.productFrame_app (Dv.product a b c h) (Dh.unitFrame a ha) (Dh.unitFrame b hb) U).symm.trans
    (congrArg (fun e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L c => e.hom.app U (1 : Γ(T.left, U))) he)

include hi in
/-- Vertical neutral frames multiply correctly under the actual horizontal product. -/
theorem vertical_units_horizontal_product {T : Over S} (a b c : T ⟶ A ⊗ X)
    (ha : a ≫ snd A X = 1) (hb : b ≫ snd A X = 1) (hc : c ≫ snd A X = 1)
    (h : FiberwiseMultiplication.ProductRel (fst A X) (snd A X) a b c) (U : T.left.Opens) :
    (Dh.product a b c h).app U ((Dv.unitFrame a ha).hom.app U (1 : Γ(T.left, U)))
      ((Dv.unitFrame b hb).hom.app U (1 : Γ(T.left, U))) =
      (Dv.unitFrame c hc).hom.app U (1 : Γ(T.left, U)) := by
  let haa := neutral_rel (snd A X) (fst A X) a ha
  let hbb := neutral_rel (snd A X) (fst A X) b hb
  let hcc := neutral_rel (snd A X) (fst A X) c hc
  have : IsIso (Bilinear.BilinearPullback.toHom (Dh.product a b c h)) := Dh.product_isIso a b c h
  let s := Bilinear.ProductFrames.productFrame (Dh.product a b c h) (Dv.unitFrame a ha) (Dv.unitFrame b hb)
  have hs : (Dv.product c c c hcc).app ⊤ (s.hom.app ⊤ (1 : Γ(T.left, ⊤)))
      (s.hom.app ⊤ (1 : Γ(T.left, ⊤))) = s.hom.app ⊤ (1 : Γ(T.left, ⊤)) := by
    have hh := hi T a a b b a c c b c h hbb h haa hcc h ⊤
      ((Dv.unitFrame a ha).hom.app ⊤ (1 : Γ(T.left, ⊤)))
      ((Dv.unitFrame a ha).hom.app ⊤ (1 : Γ(T.left, ⊤)))
      ((Dv.unitFrame b hb).hom.app ⊤ (1 : Γ(T.left, ⊤)))
      ((Dv.unitFrame b hb).hom.app ⊤ (1 : Γ(T.left, ⊤)))
    rw [Dv.unit_left a a ha haa, Dv.unit_left b b hb hbb] at hh
    change (Dv.product c c c hcc).app ⊤
      ((Bilinear.ProductFrames.productFrame (Dh.product a b c h) (Dv.unitFrame a ha) (Dv.unitFrame b hb)).hom.app ⊤ (1 : Γ(T.left, ⊤)))
      ((Bilinear.ProductFrames.productFrame (Dh.product a b c h) (Dv.unitFrame a ha) (Dv.unitFrame b hb)).hom.app ⊤ (1 : Γ(T.left, ⊤))) = _
    rw [Bilinear.ProductFrames.productFrame_app]
    exact hh
  have he : s = Dv.unitFrame c hc := Bilinear.ProductFrames.idempotent_frame_unique (Dv.product c c c hcc) s
    (Dv.unitFrame c hc) hs (Dv.unit_left c c hc hcc ⊤ _)
  exact (Bilinear.ProductFrames.productFrame_app (Dh.product a b c h) (Dv.unitFrame a ha) (Dv.unitFrame b hb) U).symm.trans
    (congrArg (fun e : AbelianModuli.HilbertConstruction.Line.Bundles.structureModule T.left ≅ Line.Fibers.fiber L c => e.hom.app U (1 : Γ(T.left, U))) he)

end

end OAI.AlgebraicGeometry.Picard.PoincareBundle.InterchangeNeutralFrames
