import OAI.RepresentationTheory.Theta.Geometric.TranslatedLineIsoPullback
import OAI.RepresentationTheory.Theta.Geometric.Normalized.PullbackComposition

/-! # Translated Line Iso Composition -/

namespace OAI.RepresentationTheory.Theta.Geometric.TranslatedLineIsoComposition

noncomputable section

/-! Translation comparisons compose on every test scheme, via the
exact native comparison for the composed translation. -/

set_option backward.isDefEq.respectTransparency false
open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem translatedMapLineIso_comp {X T : Scheme.{u}} (M : X.Modules) (t s : X ⟶ X)
    (et : (Scheme.Modules.pullback t).obj M ≅ M)
    (es : (Scheme.Modules.pullback s).obj M ≅ M)
    (x y z : T ⟶ X) (hy : y = x ≫ t) (hz : z = y ≫ s)
    (hxz : z = x ≫ (t ≫ s)) :
    (LocallyTranslatedLineIso.translatedMapLineIso M s es y z hz).hom ≫ (LocallyTranslatedLineIso.translatedMapLineIso M t et x y hy).hom =
      (LocallyTranslatedLineIso.translatedMapLineIso M (t ≫ s) (Normalized.PullbackComposition.composePullbackIso t s et es) x z hxz).hom := by
  subst z
  subst y
  simp only [LocallyTranslatedLineIso.translatedMapLineIso, Normalized.PullbackComposition.composePullbackIso, Pullback.FrameEqualities.pullbackCongr_refl_app,
    Iso.refl_trans, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc]
  have hn := (Scheme.Modules.pullbackComp x t).inv.naturality es.hom
  change (Scheme.Modules.pullback (x ≫ t)).map es.hom ≫
      ((Scheme.Modules.pullbackComp x t).app M).inv =
    ((Scheme.Modules.pullbackComp x t).app ((Scheme.Modules.pullback s).obj M)).inv ≫
      (Scheme.Modules.pullback x).map ((Scheme.Modules.pullback t).map es.hom) at hn
  rw [← Category.assoc ((Scheme.Modules.pullback (x ≫ t)).map es.hom), hn]
  have hc := FactoredPullbackFrames.pullbackComp_assoc_inv_app x t s M
  have hh := congrArg (fun a => a ≫
    (Scheme.Modules.pullback x).map ((Scheme.Modules.pullback t).map es.hom) ≫
      (Scheme.Modules.pullback x).map et.hom) hc.symm
  simpa only [Category.assoc] using hh

theorem translatedMapLineIso_comp_of_eq {X T : Scheme.{u}} (M : X.Modules) (t s w : X ⟶ X)
    (hw : t ≫ s = w)
    (et : (Scheme.Modules.pullback t).obj M ≅ M)
    (es : (Scheme.Modules.pullback s).obj M ≅ M)
    (ew : (Scheme.Modules.pullback w).obj M ≅ M)
    (hew : ((Scheme.Modules.pullbackCongr hw).app M).symm ≪≫ Normalized.PullbackComposition.composePullbackIso t s et es = ew)
    (x y z : T ⟶ X) (hy : y = x ≫ t) (hz : z = y ≫ s) (hxz : z = x ≫ w) :
    (LocallyTranslatedLineIso.translatedMapLineIso M s es y z hz).hom ≫ (LocallyTranslatedLineIso.translatedMapLineIso M t et x y hy).hom =
      (LocallyTranslatedLineIso.translatedMapLineIso M w ew x z hxz).hom := by
  subst w
  simp only [Pullback.FrameEqualities.pullbackCongr_refl_app, Iso.refl_symm, Iso.refl_trans] at hew
  rw [← hew]
  exact translatedMapLineIso_comp M t s et es x y z hy hz hxz

end

end OAI.RepresentationTheory.Theta.Geometric.TranslatedLineIsoComposition
