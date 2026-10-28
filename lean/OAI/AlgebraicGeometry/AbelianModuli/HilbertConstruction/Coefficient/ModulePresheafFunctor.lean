import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf

/-! # Module Presheaf Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor

noncomputable section

/-! A module sheaf and its actual morphisms give a functorial coefficient-module presheaf on every open set. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

def coefficientModulePresheafFunctor {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : R →+* Γ(X, ⊤)) : X.Modules ⥤ TopCat.Presheaf (ModuleCat.{u} R) X :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.forgetToPresheafModuleCat (.op (⊤ : X.Opens)) isTerminalTop.op ⋙
      (Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars f)

theorem coefficientModulePresheafFunctor_obj {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : R →+* Γ(X, ⊤)) (M : X.Modules) :
    (coefficientModulePresheafFunctor f).obj M = ModulePresheaf.coefficientModulePresheaf f M := rfl

theorem coefficientModulePresheafFunctor_map_app {X : Scheme.{u}} {R : Type u} [CommRing R]
    (f : R →+* Γ(X, ⊤)) {M N : X.Modules} (a : M ⟶ N) (U : X.Opens)
    (x : ((coefficientModulePresheafFunctor f).obj M).obj (.op U)) :
    ((coefficientModulePresheafFunctor f).map a).app (.op U) x = a.app U x := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor
