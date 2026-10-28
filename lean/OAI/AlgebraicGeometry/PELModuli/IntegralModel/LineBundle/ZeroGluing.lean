import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.SquareIsoFrames
import OAI.AlgebraicGeometry.Picard.PoincareBundle.Ordinary.SquareGluing

/-! # Zero Gluing -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.ZeroGluing

noncomputable section

section

/-! A normalized line isomorphism induces gluing that preserves the
actual frame on the zero-section line. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem lineBundleCommutingSquareIso_eq {X Y X' Y' : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f : Y ⟶ X) (v : X' ⟶ X) (r : Y' ⟶ Y) (f' : Y' ⟶ X') (h : f' ≫ v = r ≫ f) :
    SquareIsoFrames.lineBundleCommutingSquareIso L f v r f' h =
      (Picard.PoincareBundle.Ordinary.SquareGluing.pullbackSquare f f' v r h.symm).app L.sheaf := by
  apply CategoryTheory.Iso.ext
  simp only [SquareIsoFrames.lineBundleCommutingSquareIso, NormalizedRestriction.lineBundlePullbackComparison,
    Picard.PoincareBundle.Ordinary.SquareGluing.pullbackSquare, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities.pullbackCongr_refl_app, Iso.refl_inv, Category.assoc]
  rfl

theorem lineBundleSquareTransportIso_eq_native {X Y X' Y' : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f g : Y ⟶ X) (v : X' ⟶ X) (r : Y' ⟶ Y) (f' g' : Y' ⟶ X')
    (hf : f' ≫ v = r ≫ f) (hg : g' ≫ v = r ≫ g)
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf) :
    SquareIsoFrames.lineBundleSquareTransportIso L f g v r f' g' hf hg e =
      (Picard.PoincareBundle.Ordinary.SquareGluing.pullbackSquare f f' v r hf.symm).app L.sheaf ≪≫
        (Scheme.Modules.pullback r).mapIso e ≪≫
          ((Picard.PoincareBundle.Ordinary.SquareGluing.pullbackSquare g g' v r hg.symm).app L.sheaf).symm := by
  unfold SquareIsoFrames.lineBundleSquareTransportIso
  rw [lineBundleCommutingSquareIso_eq, lineBundleCommutingSquareIso_eq]

theorem lineBundleSquareFrame_eq_squareIso {X Y A B : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (z : A ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A)
    (f : Y ⟶ X) (w : B ⟶ Y) (a : B ⟶ A) (h : w ≫ f = a ≫ z) :
    SquareFrame.lineBundleSquareFrame L z frame f w a h =
      (SquareIsoFrames.lineBundleCommutingSquareIso L f z w a h.symm).symm ≪≫
        (Scheme.Modules.pullback a).mapIso frame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a := by
  apply CategoryTheory.Iso.ext
  simp only [SquareFrame.lineBundleSquareFrame, SquareIsoFrames.lineBundleCommutingSquareIso, NormalizedRestriction.lineBundlePullbackComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities.pullbackCongr_refl_app,
    Category.assoc]
  rfl

theorem lineBundleZeroGluing_preserves_frame {X Y A B : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (z : A ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A)
    (f g : Y ⟶ X) (w : B ⟶ Y) (a c : B ⟶ A)
    (hf : w ≫ f = a ≫ z) (hg : w ≫ g = c ≫ z)
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf)
    (he : (Scheme.Modules.pullback w).mapIso e ≪≫ SquareFrame.lineBundleSquareFrame L z frame g w c hg =
      SquareFrame.lineBundleSquareFrame L z frame f w a hf) :
    SquareIsoFrames.lineBundleSquareTransportIso L f g z w a c hf.symm hg.symm e ≪≫
        (Scheme.Modules.pullback c).mapIso frame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso c =
      (Scheme.Modules.pullback a).mapIso frame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a := by
  rw [lineBundleSquareFrame_eq_squareIso, lineBundleSquareFrame_eq_squareIso] at he
  have h := congrArg (fun d => SquareIsoFrames.lineBundleCommutingSquareIso L f z w a hf.symm ≪≫ d) he
  simpa only [SquareIsoFrames.lineBundleSquareTransportIso, Iso.trans_assoc, Iso.self_symm_id_assoc] using h

end

/-! Frame compatibility of the restricted zero-line gluing is the
original Poincare normalization equation, through the native squares. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

theorem lineBundleZeroGluing_normalized {X Y A B : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (z : A ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A)
    (f g : Y ⟶ X) (w : B ⟶ Y) (a c : B ⟶ A)
    (hf : w ≫ f = a ≫ z) (hg : w ≫ g = c ≫ z)
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf)
    (he : SquareIsoFrames.lineBundleSquareTransportIso L f g z w a c hf.symm hg.symm e ≪≫
        (Scheme.Modules.pullback c).mapIso frame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso c =
      (Scheme.Modules.pullback a).mapIso frame ≪≫ AbelianModuli.HilbertConstruction.Line.Bundles.structureModulePullbackIso a) :
    (Scheme.Modules.pullback w).mapIso e ≪≫ SquareFrame.lineBundleSquareFrame L z frame g w c hg =
      SquareFrame.lineBundleSquareFrame L z frame f w a hf := by
  rw [lineBundleSquareFrame_eq_squareIso, lineBundleSquareFrame_eq_squareIso]
  have h := congrArg (fun d => (SquareIsoFrames.lineBundleCommutingSquareIso L f z w a hf.symm).symm ≪≫ d) he
  simp only [SquareIsoFrames.lineBundleSquareTransportIso, Iso.trans_assoc, Iso.symm_self_id_assoc] at h
  simpa only [Iso.trans_assoc] using h

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.ZeroGluing
