import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageMates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Additive.SheafInverseImageComposition

/-! # Inverse Image Composition -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageComposition

noncomputable section

/-! The actual comparison from abelian inverse image to module pullback respects composition, by the mates correspondence for the pushforward square. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.TwoSquare
universe u

variable {X Y Z : Scheme.{u}}

theorem moduleInverseImageSquare_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z) :
    (InverseImageMates.moduleInverseImageSquare (f ≫ g)).whiskerLeft (Scheme.Modules.pullbackComp f g).inv =
      ((InverseImageMates.moduleInverseImageSquare g) ≫ᵥ (InverseImageMates.moduleInverseImageSquare f)).whiskerRight
        (Additive.SheafInverseImageComposition.additiveSheafInverseImageCompIso f.base g.base).inv := by
  let FX : X.Modules ⥤ X.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf X.ringCatSheaf
  let FY : Y.Modules ⥤ Y.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf Y.ringCatSheaf
  let FZ : Z.Modules ⥤ Z.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf Z.ringCatSheaf
  let Pf := Scheme.Modules.pullback f
  let Pg := Scheme.Modules.pullback g
  let Pc := Scheme.Modules.pullback (f ≫ g)
  let Rf := Scheme.Modules.pushforward f
  let Rg := Scheme.Modules.pushforward g
  let Rc := Scheme.Modules.pushforward (f ≫ g)
  let Lf := TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base
  let Lg := TopCat.Sheaf.pullback AddCommGrpCat.{u} g.base
  let Lc := TopCat.Sheaf.pullback AddCommGrpCat.{u} (f ≫ g).base
  let Af := TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base
  let Ag := TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base
  let Ac := TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g).base
  let sf : TwoSquare FY Pf Lf FX := InverseImageMates.moduleInverseImageSquare f
  let sg : TwoSquare FZ Pg Lg FY := InverseImageMates.moduleInverseImageSquare g
  let sc : TwoSquare FZ Pc Lc FX := InverseImageMates.moduleInverseImageSquare (f ≫ g)
  let uf : TwoSquare Rf FX FY Af := InverseImageMates.moduleUnderlyingPushforwardSquare f
  let ug : TwoSquare Rg FY FZ Ag := InverseImageMates.moduleUnderlyingPushforwardSquare g
  let uc : TwoSquare Rc FX FZ Ac := InverseImageMates.moduleUnderlyingPushforwardSquare (f ≫ g)
  let pm : Pc ⟶ Pg ⋙ Pf := (Scheme.Modules.pullbackComp f g).inv
  let pa : Lc ⟶ Lg ⋙ Lf := (Additive.SheafInverseImageComposition.additiveSheafInverseImageCompIso f.base g.base).inv
  let rm : Rf ⋙ Rg ⟶ Rc := (Scheme.Modules.pushforwardComp f g).hom
  let ra : Af ⋙ Ag ⟶ Ac := (Additive.SheafInverseImageComposition.additiveSheafPushforwardCompIso f.base g.base).hom
  let amf := Scheme.Modules.pullbackPushforwardAdjunction f
  let amg := Scheme.Modules.pullbackPushforwardAdjunction g
  let amc := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  let aaf := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f.base
  let aag := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g.base
  let aac := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (f ≫ g).base
  have ha : conjugateEquiv (aag.comp aaf) aac pa = ra :=
    Adjunction.conjugateEquiv_leftAdjointCompIso_inv aag aaf aac
      (Additive.SheafInverseImageComposition.additiveSheafPushforwardCompIso f.base g.base)
  have hm : conjugateEquiv (amg.comp amf) amc pm = rm :=
    Scheme.Modules.conjugateEquiv_pullbackComp_inv f g
  have hf : mateEquiv amf aaf sf = uf := InverseImageMates.moduleInverseImageSquare_mate f
  have hg : mateEquiv amg aag sg = ug := InverseImageMates.moduleInverseImageSquare_mate g
  have hc : mateEquiv amc aac sc = uc := InverseImageMates.moduleInverseImageSquare_mate (f ≫ g)
  have hl : mateEquiv (amg.comp amf) aac (sc.whiskerLeft pm) = uc.whiskerTop rm :=
    (conjugateEquiv_mateEquiv_vcomp (amg.comp amf) amc aac pm sc).trans
      (congrArg₂ (fun (s : TwoSquare Rc FX FZ Ac) (r : Rf ⋙ Rg ⟶ Rc) =>
        s.whiskerTop r) hc hm)
  have hv : mateEquiv (amg.comp amf) (aag.comp aaf) (sg ≫ᵥ sf) = uf ≫ₕ ug :=
    (mateEquiv_hcomp amg aag amf aaf sg sf).trans
      (congrArg₂ (fun (s : TwoSquare Rf FX FY Af) (t : TwoSquare Rg FY FZ Ag) =>
        s ≫ₕ t) hf hg)
  have hr : mateEquiv (amg.comp amf) aac ((sg ≫ᵥ sf).whiskerRight pa) =
      (uf ≫ₕ ug).whiskerBottom ra :=
    (mateEquiv_conjugateEquiv_vcomp (amg.comp amf) (aag.comp aaf) aac (sg ≫ᵥ sf) pa).trans
      (congrArg₂ (fun (s : TwoSquare (Rf ⋙ Rg) FX FZ (Af ⋙ Ag))
        (r : Af ⋙ Ag ⟶ Ac) => s.whiskerBottom r) hv ha)
  have hp : uc.whiskerTop rm = (uf ≫ₕ ug).whiskerBottom ra := by
    ext M
    rfl
  change sc.whiskerLeft pm = (sg ≫ᵥ sf).whiskerRight pa
  exact (mateEquiv (amg.comp amf) aac).injective (hl.trans (hp.trans hr.symm))

theorem moduleInverseImageComparison_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    InverseImageComparison.moduleInverseImageComparison (f ≫ g) M ≫
      (SheafOfModules.toSheaf X.ringCatSheaf).map ((Scheme.Modules.pullbackComp f g).inv.app M) =
    (Additive.SheafInverseImageComposition.additiveSheafInverseImageCompIso f.base g.base).inv.app
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj M) ≫
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base).map (InverseImageComparison.moduleInverseImageComparison g M) ≫
        InverseImageComparison.moduleInverseImageComparison f ((Scheme.Modules.pullback g).obj M) := by
  let FX : X.Modules ⥤ X.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf X.ringCatSheaf
  let FY : Y.Modules ⥤ Y.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf Y.ringCatSheaf
  let FZ : Z.Modules ⥤ Z.carrier.Sheaf AddCommGrpCat.{u} := SheafOfModules.toSheaf Z.ringCatSheaf
  let Pf := Scheme.Modules.pullback f
  let Pg := Scheme.Modules.pullback g
  let Pc := Scheme.Modules.pullback (f ≫ g)
  let Lf := TopCat.Sheaf.pullback AddCommGrpCat.{u} f.base
  let Lg := TopCat.Sheaf.pullback AddCommGrpCat.{u} g.base
  let Lc := TopCat.Sheaf.pullback AddCommGrpCat.{u} (f ≫ g).base
  let sf : TwoSquare FY Pf Lf FX := InverseImageMates.moduleInverseImageSquare f
  let sg : TwoSquare FZ Pg Lg FY := InverseImageMates.moduleInverseImageSquare g
  let sc : TwoSquare FZ Pc Lc FX := InverseImageMates.moduleInverseImageSquare (f ≫ g)
  let pm : Pc ⟶ Pg ⋙ Pf := (Scheme.Modules.pullbackComp f g).inv
  let pa : Lc ⟶ Lg ⋙ Lf := (Additive.SheafInverseImageComposition.additiveSheafInverseImageCompIso f.base g.base).inv
  have h : (sc.whiskerLeft pm).app M = ((sg ≫ᵥ sf).whiskerRight pa).app M :=
    congr_app (moduleInverseImageSquare_comp_inv f g) M
  have hv : (sg ≫ᵥ sf).app M = Lf.map (sg.app M) ≫ sf.app (Pg.obj M) := by
    change (𝟙 _ ≫ Lf.map (sg.app M) ≫ 𝟙 _ ≫ sf.app (Pg.obj M) ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
  have h' : sc.app M ≫ FX.map (pm.app M) =
      pa.app (FZ.obj M) ≫ Lf.map (sg.app M) ≫ sf.app (Pg.obj M) :=
    h.trans (congrArg (fun v => pa.app (FZ.obj M) ≫ v) hv)
  have hc : sc.app M = InverseImageComparison.moduleInverseImageComparison (f ≫ g) M := InverseImageMates.moduleInverseImageSquare_app _ _
  have hg : sg.app M = InverseImageComparison.moduleInverseImageComparison g M := InverseImageMates.moduleInverseImageSquare_app _ _
  have hf : sf.app (Pg.obj M) = InverseImageComparison.moduleInverseImageComparison f (Pg.obj M) :=
    InverseImageMates.moduleInverseImageSquare_app _ _
  exact (congrArg (fun v => v ≫ FX.map (pm.app M)) hc).symm.trans
    (h'.trans (congrArg₂ (fun v w => pa.app (FZ.obj M) ≫ Lf.map v ≫ w) hg hf))

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.InverseImageComposition
