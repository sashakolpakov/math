import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.PullbackUnits
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.LocalLineIsoGluing

/-! # Unit Local Isos -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.UnitLocalIsos

noncomputable section

/-! Local line isomorphisms expressed through adjunction units, so
their action on every subordinate open is retained exactly. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry

namespace Construction

universe u
variable {X : Scheme.{u}}

theorem open_pullback_unit_over_isIso (M : X.Modules) (U : X.Opens) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).over U) := by
  let F := SheafOfModules.forget (X.ringCatSheaf.over U) ⋙
    PresheafOfModules.toPresheaf (X.ringCatSheaf.over U).obj
  have : IsIso (F.map (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).over U)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V
    exact PullbackUnits.Construction.open_pullback_unit_app_isIso M U V.unop.left V.unop.hom.le
  exact isIso_of_reflects_iso _ F

theorem open_pullback_unit_val_app_isIso (M : X.Modules) (U W : X.Opens) (hW : W ≤ U) :
    IsIso (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).val.app (.op W)) := by
  have := open_pullback_unit_over_isIso M U
  exact (SheafOfModules.evaluation (X.ringCatSheaf.over U)
    (.op (Over.mk (homOfLE hW)))).map_isIso
      (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).over U)

def unitLocalLineIsoOver (L M : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ (Scheme.Modules.pullback U.ι).obj M) :
    L.over U ≅ M.over U := by
  have := open_pullback_unit_over_isIso L U
  have := open_pullback_unit_over_isIso M U
  exact asIso (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L).over U) ≪≫
    (SheafOfModules.overFunctor X.ringCatSheaf U).mapIso
      ((Scheme.Modules.pushforward U.ι).mapIso e) ≪≫
    (asIso (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).over U)).symm

theorem unitLocalLineIsoOver_fac (L M : X.Modules) (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ (Scheme.Modules.pullback U.ι).obj M) :
    (unitLocalLineIsoOver L M U e).hom ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).over U =
      ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L).over U ≫
        ((Scheme.Modules.pushforward U.ι).map e.hom).over U := by
  have := open_pullback_unit_over_isIso M U
  dsimp only [unitLocalLineIsoOver, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv]
  rw [Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rfl

theorem unitLocalLineIsoOver_app_fac (L M : X.Modules) (U W : X.Opens) (hW : W ≤ U)
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ (Scheme.Modules.pullback U.ι).obj M) :
    (LocalLineIsoGluing.Construction.localModuleIsoAt (unitLocalLineIsoOver L M U e) hW).hom ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).val.app (.op W) =
      ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L).val.app (.op W) ≫
        ((Scheme.Modules.pushforward U.ι).map e.hom).val.app (.op W) :=
  congrArg (fun a => a.val.app (.op (Over.mk (homOfLE hW))))
    (unitLocalLineIsoOver_fac L M U e)

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.UnitLocalIsos
