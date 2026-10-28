import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.UnitContinuation
import OAI.AlgebraicGeometry.AbelianScheme.CentralAction.UnitLocalIsos

/-! # Open Line Overlap -/

namespace OAI.AlgebraicGeometry.AbelianScheme.CentralAction.OpenLineOverlap

noncomputable section

/-! Native agreement on a smaller open implies literal agreement of
the section maps used to glue the line-bundle isomorphisms. -/

set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace Construction

universe u
variable {S : Scheme.{u}}

theorem local_comparison_section_transport {C : Type*} [Category C]
    {A B D E : C} (c : A ⟶ B) (η : B ⟶ D) (t : D ⟶ E)
    (η' : B ⟶ E) (α : A ⟶ D) (α' : A ⟶ E)
    (hη : η ≫ t = η') (hα : α ≫ t = α') (hc : c ≫ η = α) :
    c ≫ η' = α' := by rw [← hη, ← Category.assoc, hc, hα]

def lineOpenOver (X : Over S) (U : X.left.Opens) : Over S := Over.mk (U.ι ≫ X.hom)

def lineOpenInclusion (X : Over S) (U : X.left.Opens) : lineOpenOver X U ⟶ X :=
  Over.homMk U.ι rfl

def lineOpenSubinclusion (X : Over S) {U V : X.left.Opens} (h : V ≤ U) :
    lineOpenOver X V ⟶ lineOpenOver X U :=
  Over.homMk (X.left.homOfLE h) (by
    change X.left.homOfLE h ≫ U.ι ≫ X.hom = V.ι ≫ X.hom
    rw [← Category.assoc, X.left.homOfLE_ι h])

theorem lineOpenSubinclusion_comp (X : Over S) {U V : X.left.Opens} (h : V ≤ U) :
    lineOpenSubinclusion X h ≫ lineOpenInclusion X U = lineOpenInclusion X V :=
  Over.OverMorphism.ext (X.left.homOfLE_ι h)

def lineOpenPullHom (X : Over S) (L M : X.left.Modules)
    (U W : X.left.Opens) (hW : W ≤ U)
    (a : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj M) :
    (Scheme.Modules.pullback W.ι).obj L ⟶ (Scheme.Modules.pullback W.ι).obj M :=
  pullHom (F := LinePullHom.Construction.overSchemeModulePullbacks S) (M₁ := L) (M₂ := M)
    (f₁ := lineOpenInclusion X U) (f₂ := lineOpenInclusion X U) a
    (lineOpenSubinclusion X hW) (lineOpenInclusion X W) (lineOpenInclusion X W)
    (lineOpenSubinclusion_comp X hW) (lineOpenSubinclusion_comp X hW)

def lineOpenUnitContinuation (X : Over S) (U W : X.left.Opens) (hW : W ≤ U)
    (M : X.left.Modules) :
    (Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj M) ⟶
      (Scheme.Modules.pushforward W.ι).obj ((Scheme.Modules.pullback W.ι).obj M) :=
  UnitContinuation.Construction.lineUnitContinuation (lineOpenInclusion X U) (lineOpenSubinclusion X hW)
    (lineOpenInclusion X W) (lineOpenSubinclusion_comp X hW) M

theorem lineOpenUnitContinuation_unit (X : Over S) (U W : X.left.Opens) (hW : W ≤ U)
    (M : X.left.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M ≫
        lineOpenUnitContinuation X U W hW M =
      (Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app M :=
  UnitContinuation.Construction.lineUnitContinuation_unit (lineOpenInclusion X U) (lineOpenSubinclusion X hW)
    (lineOpenInclusion X W) (lineOpenSubinclusion_comp X hW) M

theorem lineOpenUnitContinuation_comparison (X : Over S) (L M : X.left.Modules)
    (U W : X.left.Opens) (hW : W ≤ U)
    (a : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj M) :
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L ≫
        (Scheme.Modules.pushforward U.ι).map a ≫ lineOpenUnitContinuation X U W hW M =
      (Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app L ≫
        (Scheme.Modules.pushforward W.ι).map (lineOpenPullHom X L M U W hW a) :=
  UnitContinuation.Construction.lineUnitContinuation_pullHom (lineOpenInclusion X U) (lineOpenSubinclusion X hW)
    (lineOpenInclusion X W) (lineOpenSubinclusion_comp X hW) L M a

theorem lineOpenUnitContinuation_unit_app (X : Over S) (U W : X.left.Opens) (hW : W ≤ U)
    (M : X.left.Modules) :
    ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app M).val.app (.op W) ≫
        (lineOpenUnitContinuation X U W hW M).val.app (.op W) =
      ((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app M).val.app (.op W) :=
  congrArg (fun q => q.val.app (.op W)) (lineOpenUnitContinuation_unit X U W hW M)

theorem lineOpenUnitContinuation_comparison_app (X : Over S) (L M : X.left.Modules)
    (U W : X.left.Opens) (hW : W ≤ U)
    (a : (Scheme.Modules.pullback U.ι).obj L ⟶ (Scheme.Modules.pullback U.ι).obj M) :
    (((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app L).val.app (.op W) ≫
        ((Scheme.Modules.pushforward U.ι).map a).val.app (.op W)) ≫
          (lineOpenUnitContinuation X U W hW M).val.app (.op W) =
      ((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app L).val.app (.op W) ≫
        ((Scheme.Modules.pushforward W.ι).map (lineOpenPullHom X L M U W hW a)).val.app (.op W) :=
  congrArg (fun q => q.val.app (.op W)) (lineOpenUnitContinuation_comparison X L M U W hW a)

theorem unitLocalLineIsoOver_common_fac (X : Over S) (L M : X.left.Modules)
    (U W : X.left.Opens) (hW : W ≤ U)
    (a : (Scheme.Modules.pullback U.ι).obj L ≅ (Scheme.Modules.pullback U.ι).obj M) :
    (LocalLineIsoGluing.Construction.localModuleIsoAt (UnitLocalIsos.Construction.unitLocalLineIsoOver L M U a) hW).hom ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app M).val.app (.op W) =
      ((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app L).val.app (.op W) ≫
        ((Scheme.Modules.pushforward W.ι).map (lineOpenPullHom X L M U W hW a.hom)).val.app (.op W) := by
  exact local_comparison_section_transport _ _ _ _ _ _
    (lineOpenUnitContinuation_unit_app X U W hW M)
    (lineOpenUnitContinuation_comparison_app X L M U W hW a.hom)
    (UnitLocalIsos.Construction.unitLocalLineIsoOver_app_fac L M U W hW a)

theorem unitLocalLineIsoOver_overlap (X : Over S) (L M : X.left.Modules)
    (U V W : X.left.Opens) (hU : W ≤ U) (hV : W ≤ V)
    (a : (Scheme.Modules.pullback U.ι).obj L ≅ (Scheme.Modules.pullback U.ι).obj M)
    (b : (Scheme.Modules.pullback V.ι).obj L ≅ (Scheme.Modules.pullback V.ι).obj M)
    (hab : lineOpenPullHom X L M U W hU a.hom = lineOpenPullHom X L M V W hV b.hom) :
    (LocalLineIsoGluing.Construction.localModuleIsoAt (UnitLocalIsos.Construction.unitLocalLineIsoOver L M U a) hU).hom =
      (LocalLineIsoGluing.Construction.localModuleIsoAt (UnitLocalIsos.Construction.unitLocalLineIsoOver L M V b) hV).hom := by
  have := UnitLocalIsos.Construction.open_pullback_unit_val_app_isIso M W W le_rfl
  apply (cancel_mono
    (((Scheme.Modules.pullbackPushforwardAdjunction W.ι).unit.app M).val.app (.op W))).mp
  rw [unitLocalLineIsoOver_common_fac, unitLocalLineIsoOver_common_fac, hab]

end Construction

end

end OAI.AlgebraicGeometry.AbelianScheme.CentralAction.OpenLineOverlap
