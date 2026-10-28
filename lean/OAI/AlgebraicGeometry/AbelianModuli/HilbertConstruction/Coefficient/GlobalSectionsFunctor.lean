import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheaf

/-! # Global Sections Functor -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor

noncomputable section

/-! The actual global sections of a sheaf of modules, as modules over a chosen coefficient ring, form a functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

def coefficientGlobalSectionsFunctor (f : R →+* Γ(X, ⊤)) : X.Modules ⥤ ModuleCat.{u} R :=
  SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.forgetToPresheafModuleCat (.op (⊤ : X.Opens)) isTerminalTop.op ⋙
      (evaluation _ _).obj (.op (⊤ : X.Opens)) ⋙ ModuleCat.restrictScalars f

def schemeGlobalSectionsFunctor (p : X ⟶ Spec (.of R)) : X.Modules ⥤ ModuleCat.{u} R :=
  coefficientGlobalSectionsFunctor (ModulePresheaf.schemeCoefficientMap p)

theorem schemeGlobalSectionsFunctor_obj (p : X ⟶ Spec (.of R)) (M : X.Modules) :
    (schemeGlobalSectionsFunctor p).obj M = (ModulePresheaf.schemeModulePresheaf p M).obj (.op ⊤) := rfl

def schemeGlobalSectionsIso (p : X ⟶ Spec (.of R)) {M N : X.Modules} (e : M ≅ N) :
    (schemeGlobalSectionsFunctor p).obj M ≃ₗ[R] (schemeGlobalSectionsFunctor p).obj N :=
  ((schemeGlobalSectionsFunctor p).mapIso e).toLinearEquiv

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.GlobalSectionsFunctor
