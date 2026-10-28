import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Module Frames -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Open.ModuleFrames.Restriction

noncomputable section

/-! Transport actual free frames on an open subscheme to the corresponding slice site. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {X : Scheme.{0}} (U : X.Opens)

def overModuleEquiv :
    SheafOfModules.{0} (X.ringCatSheaf.over U) ≌ SheafOfModules.{0} U.toScheme.ringCatSheaf :=
  Scheme.Modules.overEquiv U

def overEquivUnitIso :
    (overModuleEquiv U).functor.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  (Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf) ≪≫
    Scheme.Modules.restrictUnitIso U.ι

def overEquivInverseUnitIso :
    SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      (overModuleEquiv U).inverse.obj (SheafOfModules.unit U.toScheme.ringCatSheaf) :=
  (overModuleEquiv U).unitIso.app (SheafOfModules.unit (X.ringCatSheaf.over U)) ≪≫
    (overModuleEquiv U).inverse.mapIso (overEquivUnitIso U)

def overFreeIso (M : X.Modules) (I : Type)
    (e : SheafOfModules.free (R := U.toScheme.ringCatSheaf) I ≅ M.restrict U.ι) :
    SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U :=
  SheafOfModules.mapFreeIso (overModuleEquiv U).inverse I (overEquivInverseUnitIso U) ≪≫
    (overModuleEquiv U).inverse.mapIso e ≪≫
    (overModuleEquiv U).inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    ((overModuleEquiv U).unitIso.app (M.over U)).symm

end

end OAI.AlgebraicGeometry.Comparison.Betti.Open.ModuleFrames.Restriction
