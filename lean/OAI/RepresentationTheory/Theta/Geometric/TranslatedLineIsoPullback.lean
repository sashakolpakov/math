import OAI.RepresentationTheory.Theta.Geometric.LocallyTranslatedLineIso
import OAI.RepresentationTheory.Theta.Geometric.Pullback.FrameEqualities

/-! # Translated Line Iso Pullback -/

namespace OAI.RepresentationTheory.Theta.Geometric.TranslatedLineIsoPullback

noncomputable section

/-! The actual translated comparison commutes with arbitrary further
pullback, with all composition maps retained. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem translatedMapLineIso_pullback {X T U : Scheme.{u}} (M : X.Modules) (t : X ⟶ X)
    (e : (Scheme.Modules.pullback t).obj M ≅ M) (x y : T ⟶ X) (h : y = x ≫ t) (r : U ⟶ T)
    (hr : r ≫ y = (r ≫ x) ≫ t) :
    ((Scheme.Modules.pullbackComp r y).app M).inv ≫
      (Scheme.Modules.pullback r).map (LocallyTranslatedLineIso.translatedMapLineIso M t e x y h).hom ≫
        ((Scheme.Modules.pullbackComp r x).app M).hom =
      (LocallyTranslatedLineIso.translatedMapLineIso M t e (r ≫ x) (r ≫ y) hr).hom := by
  subst y
  simp only [LocallyTranslatedLineIso.translatedMapLineIso, Pullback.FrameEqualities.pullbackCongr_refl_app, Iso.refl_trans,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp]
  have hn := (Scheme.Modules.pullbackComp r x).hom.naturality e.hom
  change (Scheme.Modules.pullback r).map ((Scheme.Modules.pullback x).map e.hom) ≫
      ((Scheme.Modules.pullbackComp r x).app M).hom =
    ((Scheme.Modules.pullbackComp r x).app ((Scheme.Modules.pullback t).obj M)).hom ≫
      (Scheme.Modules.pullback (r ≫ x)).map e.hom at hn
  simp only [Category.assoc]
  rw [hn]
  have hc := FactoredPullbackFrames.pullbackComp_assoc_inv_app r x t M
  have hh := congrArg (fun a => a ≫
    ((Scheme.Modules.pullbackComp r x).app ((Scheme.Modules.pullback t).obj M)).hom ≫
      (Scheme.Modules.pullback (r ≫ x)).map e.hom) hc
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh

end

end OAI.RepresentationTheory.Theta.Geometric.TranslatedLineIsoPullback
