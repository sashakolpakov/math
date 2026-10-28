import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.NormalizedRestriction

/-! # Square Iso Frames -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareIsoFrames

noncomputable section

section

/-! The native line-bundle comparison of a commuting square preserves
the frames induced by a commuting square of zero sections. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

def lineBundleCommutingSquareIso {X Y X' Y' : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f : Y ⟶ X) (v : X' ⟶ X) (r : Y' ⟶ Y) (f' : Y' ⟶ X') (h : f' ≫ v = r ≫ f) :
    ((L.pullback v).pullback f').sheaf ≅ ((L.pullback f).pullback r).sheaf :=
  NormalizedRestriction.lineBundlePullbackComparison L f' v (r ≫ f) h ≪≫
    (NormalizedRestriction.lineBundlePullbackComparison L r f (r ≫ f) rfl).symm

theorem lineBundleCommutingSquareIso_frame {X Y X' Y' A B A' B' : Scheme.{0}}
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (z : A ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A)
    (f : Y ⟶ X) (w : B ⟶ Y) (a : B ⟶ A) (hf : w ≫ f = a ≫ z)
    (v : X' ⟶ X) (z' : A' ⟶ X') (p : A' ⟶ A) (hz : z' ≫ v = p ≫ z)
    (r : Y' ⟶ Y) (w' : B' ⟶ Y') (d : B' ⟶ B) (hw : w' ≫ r = d ≫ w)
    (f' : Y' ⟶ X') (a' : B' ⟶ A') (hf' : w' ≫ f' = a' ≫ z')
    (hs : f' ≫ v = r ≫ f) (ha : a' ≫ p = d ≫ a) :
    (Scheme.Modules.pullback w').mapIso (lineBundleCommutingSquareIso L f v r f' hs) ≪≫
      SquareFrame.lineBundleSquareFrame (L.pullback f) w (SquareFrame.lineBundleSquareFrame L z frame f w a hf) r w' d hw =
    SquareFrame.lineBundleSquareFrame (L.pullback v) z' (SquareFrame.lineBundleSquareFrame L z frame v z' p hz) f' w' a' hf' := by
  have hcomp : w' ≫ (r ≫ f) = (d ≫ a) ≫ z := by
    rw [← Category.assoc, hw, Category.assoc, hf, ← Category.assoc]
  rw [NormalizedRestriction.lineBundleSquareFrame_factor L z frame f w a hf r w' d hw (r ≫ f) (d ≫ a) rfl rfl hcomp,
    NormalizedRestriction.lineBundleSquareFrame_factor L z frame v z' p hz f' w' a' hf' (r ≫ f) (d ≫ a) hs ha hcomp]
  simp only [lineBundleCommutingSquareIso, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc]

end

/-! Scalar transport through two commuting squares preserves the
original prescribed normalization on a compatible zero-section square. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

def lineBundleSquareTransportIso {X Y X' Y' : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f g : Y ⟶ X) (v : X' ⟶ X) (r : Y' ⟶ Y) (f' g' : Y' ⟶ X')
    (hf : f' ≫ v = r ≫ f) (hg : g' ≫ v = r ≫ g)
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf) :
    ((L.pullback v).pullback f').sheaf ≅ ((L.pullback v).pullback g').sheaf :=
  lineBundleCommutingSquareIso L f v r f' hf ≪≫ (Scheme.Modules.pullback r).mapIso e ≪≫
    (lineBundleCommutingSquareIso L g v r g' hg).symm

theorem lineBundleSquareTransportIso_normalized {X Y X' Y' A B A' B' : Scheme.{0}}
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (z : A ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A)
    (f g : Y ⟶ X) (w : B ⟶ Y) (a c : B ⟶ A)
    (hf : w ≫ f = a ≫ z) (hg : w ≫ g = c ≫ z)
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf)
    (he : (Scheme.Modules.pullback w).mapIso e ≪≫ SquareFrame.lineBundleSquareFrame L z frame g w c hg =
      SquareFrame.lineBundleSquareFrame L z frame f w a hf)
    (v : X' ⟶ X) (z' : A' ⟶ X') (p : A' ⟶ A) (hz : z' ≫ v = p ≫ z)
    (r : Y' ⟶ Y) (w' : B' ⟶ Y') (d : B' ⟶ B) (hw : w' ≫ r = d ≫ w)
    (f' g' : Y' ⟶ X') (a' c' : B' ⟶ A')
    (hf' : w' ≫ f' = a' ≫ z') (hg' : w' ≫ g' = c' ≫ z')
    (hs : f' ≫ v = r ≫ f) (ht : g' ≫ v = r ≫ g)
    (ha : a' ≫ p = d ≫ a) (hc : c' ≫ p = d ≫ c) :
    (Scheme.Modules.pullback w').mapIso (lineBundleSquareTransportIso L f g v r f' g' hs ht e) ≪≫
      SquareFrame.lineBundleSquareFrame (L.pullback v) z' (SquareFrame.lineBundleSquareFrame L z frame v z' p hz) g' w' c' hg' =
      SquareFrame.lineBundleSquareFrame (L.pullback v) z' (SquareFrame.lineBundleSquareFrame L z frame v z' p hz) f' w' a' hf' := by
  have hS := lineBundleCommutingSquareIso_frame L z frame f w a hf v z' p hz r w' d hw f' a' hf' hs ha
  have hT := lineBundleCommutingSquareIso_frame L z frame g w c hg v z' p hz r w' d hw g' c' hg' ht hc
  have hN := GlobalSquareFrame.lineBundleSquareFrame_naturality (L.pullback f) (L.pullback g) e w
    (SquareFrame.lineBundleSquareFrame L z frame g w c hg) r w' d hw
  rw [he] at hN
  rw [← hS, ← hT]
  simp only [lineBundleSquareTransportIso, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [hN]

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareIsoFrames
