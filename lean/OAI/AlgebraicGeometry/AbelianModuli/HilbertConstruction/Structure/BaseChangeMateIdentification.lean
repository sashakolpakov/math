import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.SheafBaseChange

/-! # Base Change Mate Identification -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeMateIdentification

noncomputable section

/-! The structure-sheaf base-change morphism defined from functions is the canonical adjunction mate, followed by the actual pullback identification of the structure sheaf. -/
open _root_.CategoryTheory _root_.AlgebraicGeometry
universe u
variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback a b f g)

theorem schemeModuleBaseChange_normalization (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((SchemeModule.SchemeModuleBaseChange.map H).app M) =
      (Scheme.Modules.pushforward f).map
          ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) ≫
        (SchemeModule.SchemeModuleBaseChange.pushforwardSquareIso H).hom.app
          ((Scheme.Modules.pullback a).obj M) :=
  (unit_mateEquiv_symm (Scheme.Modules.pullbackPushforwardAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (TwoSquare.mk _ _ _ _ (SchemeModule.SchemeModuleBaseChange.pushforwardSquareIso H).hom) M).symm

theorem structureBaseChangeMap_eq_mate :
    SheafBaseChange.structureBaseChangeMap H =
      (SchemeModule.SchemeModuleBaseChange.map H).app (Line.Bundles.structureModule X) ≫
        (Scheme.Modules.pushforward b).map (Line.Bundles.structureModulePullbackIso a).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [SheafBaseChange.structureBaseChangeMap_normalization, Adjunction.homEquiv_naturality_right,
    schemeModuleBaseChange_normalization]
  let μ := (Line.Bundles.structureModulePullbackIso a).hom
  let e := SchemeModule.SchemeModuleBaseChange.pushforwardSquareIso H
  let η := (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app (Line.Bundles.structureModule X)
  let κ := SheafOfModules.unitToPushforwardObjUnit a.toRingCatSheafHom
  have hu : η ≫ (Scheme.Modules.pushforward a).map μ = κ := by
    have : (SheafOfModules.pushforward a.toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward a).IsRightAdjoint
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      a.toRingCatSheafHom
  have hn : (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforward a).map μ) ≫
        e.hom.app (Line.Bundles.structureModule P) =
      e.hom.app ((Scheme.Modules.pullback a).obj (Line.Bundles.structureModule X)) ≫
        (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforward b).map μ) :=
    e.hom.naturality μ
  have hα : SheafBaseChange.structureBaseChangeAdjoint H =
      (Scheme.Modules.pushforward f).map κ ≫ e.hom.app (Line.Bundles.structureModule P) := rfl
  calc
    SheafBaseChange.structureBaseChangeAdjoint H =
        (Scheme.Modules.pushforward f).map κ ≫ e.hom.app (Line.Bundles.structureModule P) := hα
    _ = (Scheme.Modules.pushforward f).map
        (η ≫ (Scheme.Modules.pushforward a).map μ) ≫ e.hom.app (Line.Bundles.structureModule P) :=
      congrArg (fun z => (Scheme.Modules.pushforward f).map z ≫ e.hom.app (Line.Bundles.structureModule P)) hu.symm
    _ = _ := by
      rw [Functor.map_comp, Category.assoc, hn, ← Category.assoc]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Structure.BaseChangeMateIdentification
