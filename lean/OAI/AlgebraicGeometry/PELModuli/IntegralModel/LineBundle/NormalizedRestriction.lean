import OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.GlobalSquareFrame

/-! # Normalized Restriction -/

namespace OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.NormalizedRestriction

noncomputable section

/-! Normalized isomorphisms between two different pullbacks restrict
through section squares with the original prescribed frames. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

def lineBundlePullbackComparison {X Y Z : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (r : Z ⟶ Y) (f : Y ⟶ X) (f' : Z ⟶ X) (hf : r ≫ f = f') :
    ((L.pullback f).pullback r).sheaf ≅ (L.pullback f').sheaf :=
  (Scheme.Modules.pullbackComp r f).app L.sheaf ≪≫ (Scheme.Modules.pullbackCongr hf).app L.sheaf

theorem lineBundleSquareFrame_factor {X Y Z A B C : Scheme.{0}}
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (z : A ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A)
    (f : Y ⟶ X) (w : B ⟶ Y) (a : B ⟶ A) (h : w ≫ f = a ≫ z)
    (r : Z ⟶ Y) (w' : C ⟶ Z) (b : C ⟶ B) (hw : w' ≫ r = b ≫ w)
    (f' : Z ⟶ X) (a' : C ⟶ A) (hf : r ≫ f = f') (ha : b ≫ a = a')
    (h' : w' ≫ f' = a' ≫ z) :
    SquareFrame.lineBundleSquareFrame (L.pullback f) w (SquareFrame.lineBundleSquareFrame L z frame f w a h) r w' b hw =
      (Scheme.Modules.pullback w').mapIso (lineBundlePullbackComparison L r f f' hf) ≪≫
        SquareFrame.lineBundleSquareFrame L z frame f' w' a' h' := by
  subst f'
  subst a'
  simpa only [lineBundlePullbackComparison, RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities.pullbackCongr_refl_app, Iso.trans_refl] using
    GlobalSquareFrame.lineBundleSquareFrame_comp L z frame r f w' w b a hw h h'

def lineBundleRestrictIso {X Y Z : Scheme.{0}} (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X)
    (f g : Y ⟶ X) (r : Z ⟶ Y) (f' g' : Z ⟶ X)
    (hf : r ≫ f = f') (hg : r ≫ g = g')
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf) :
    (L.pullback f').sheaf ≅ (L.pullback g').sheaf :=
  (lineBundlePullbackComparison L r f f' hf).symm ≪≫
    (Scheme.Modules.pullback r).mapIso e ≪≫ lineBundlePullbackComparison L r g g' hg

theorem lineBundleRestrictIso_normalized {X Y Z A B C : Scheme.{0}}
    (L : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle X) (z : A ⟶ X) (frame : (L.pullback z).sheaf ≅ AbelianModuli.HilbertConstruction.Line.Bundles.structureModule A)
    (f g : Y ⟶ X) (w : B ⟶ Y) (a c : B ⟶ A)
    (h : w ≫ f = a ≫ z) (k : w ≫ g = c ≫ z)
    (e : (L.pullback f).sheaf ≅ (L.pullback g).sheaf)
    (he : (Scheme.Modules.pullback w).mapIso e ≪≫ SquareFrame.lineBundleSquareFrame L z frame g w c k =
      SquareFrame.lineBundleSquareFrame L z frame f w a h)
    (r : Z ⟶ Y) (w' : C ⟶ Z) (b : C ⟶ B) (hw : w' ≫ r = b ≫ w)
    (f' g' : Z ⟶ X) (a' c' : C ⟶ A)
    (hf : r ≫ f = f') (hg : r ≫ g = g') (ha : b ≫ a = a') (hc : b ≫ c = c')
    (h' : w' ≫ f' = a' ≫ z) (k' : w' ≫ g' = c' ≫ z) :
    (Scheme.Modules.pullback w').mapIso (lineBundleRestrictIso L f g r f' g' hf hg e) ≪≫
      SquareFrame.lineBundleSquareFrame L z frame g' w' c' k' = SquareFrame.lineBundleSquareFrame L z frame f' w' a' h' := by
  have hn := GlobalSquareFrame.lineBundleSquareFrame_naturality (L.pullback f) (L.pullback g) e w
    (SquareFrame.lineBundleSquareFrame L z frame g w c k) r w' b hw
  rw [he] at hn
  rw [lineBundleSquareFrame_factor L z frame g w c k r w' b hw g' c' hg hc k',
    lineBundleSquareFrame_factor L z frame f w a h r w' b hw f' a' hf ha h'] at hn
  have hh := congrArg (fun q =>
    ((Scheme.Modules.pullback w').mapIso (lineBundlePullbackComparison L r f f' hf)).symm ≪≫ q) hn
  simpa only [lineBundleRestrictIso, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc] using hh

end

end OAI.AlgebraicGeometry.PELModuli.IntegralModel.LineBundle.NormalizedRestriction
