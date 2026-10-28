import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.PullbackUnits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

/-! # Section Global Value -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SectionGlobalValue

noncomputable section

/-! The global value of an actual pulled-back section is the adjunction-unit image of its original global value. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

theorem pullbackSection_globalValue {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} (s : Line.Bundles.structureModule Y ⟶ M) :
    Global.Sections.moduleSectionHomEquiv ((Scheme.Modules.pullback f).obj M) (Ample.LineBundles.pullbackSection f s) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ (Global.Sections.moduleSectionHomEquiv M s) := by
  let e := Line.Bundles.structureModulePullbackIso f
  let v : Line.Bundles.structureModule Y ⟶ (Scheme.Modules.pushforward f).obj (Line.Bundles.structureModule X) :=
    SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  have he : e.hom ≫ Ample.LineBundles.pullbackSection f s = (Scheme.Modules.pullback f).map s := by
    simp only [Ample.LineBundles.pullbackSection, e, Iso.hom_inv_id_assoc]
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (Line.Bundles.structureModule Y) ≫
      (Scheme.Modules.pushforward f).map e.hom = v := Tensor.PullbackUnits.structureModulePullbackIso_unit f
  have h : v ≫ (Scheme.Modules.pushforward f).map (Ample.LineBundles.pullbackSection f s) =
      s ≫ (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
    rw [← hu, Category.assoc, ← Functor.map_comp, he]
    exact ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality s).symm
  have hv := congrArg (fun c : Line.Bundles.structureModule Y ⟶
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj M) =>
        c.app ⊤ (1 : Γ(Y, ⊤))) h
  change (Ample.LineBundles.pullbackSection f s).app ⊤ (f.appTop (1 : Γ(Y, ⊤))) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ (s.app ⊤ (1 : Γ(Y, ⊤))) at hv
  rw [show f.appTop (1 : Γ(Y, ⊤)) = 1 from map_one f.appTop.hom] at hv
  exact hv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Pullback.SectionGlobalValue
