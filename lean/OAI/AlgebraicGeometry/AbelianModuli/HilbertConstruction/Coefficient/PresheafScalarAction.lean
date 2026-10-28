import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ScalarRingAction
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Presheaf Scalar Action -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PresheafScalarAction

noncomputable section

/-! Scalar actions on module sheaves give natural coefficient-linear endomorphisms of their section presheaves. Coefficient scalars act by the prescribed module action. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

instance coefficientSectionPresheafPreadditive {X : Scheme.{u}} {R : Type u} [CommRing R] :
    Preadditive (TopCat.Presheaf (ModuleCat.{u} R) X) :=
  inferInstanceAs (Preadditive (X.Opensᵒᵖ ⥤ ModuleCat.{u} R))

variable {X : Scheme.{u}} {R : Type u} [CommRing R]
variable (f : R →+* Γ(X, ⊤)) (M : X.Modules)

def coefficientPresheafEndRingHom : End M →+* End (ModulePresheaf.coefficientModulePresheaf f M) where
  toFun := (ModulePresheafFunctor.coefficientModulePresheafFunctor f).map
  map_one' := (ModulePresheafFunctor.coefficientModulePresheafFunctor f).map_id M
  map_mul' a b := (ModulePresheafFunctor.coefficientModulePresheafFunctor f).map_comp b a
  map_zero' := rfl
  map_add' _ _ := rfl

def coefficientPresheafGlobalScalarRingHom : Γ(X, ⊤) →+* End (ModulePresheaf.coefficientModulePresheaf f M) :=
  (coefficientPresheafEndRingHom f M).comp (Global.ScalarRingAction.globalModuleScalarRingHom M)

theorem coefficientPresheafGlobalScalarRingHom_coefficient (r : R) (U : X.Opens)
    (x : (ModulePresheaf.coefficientModulePresheaf f M).obj (.op U)) :
    (coefficientPresheafGlobalScalarRingHom f M (f r)).app (.op U) x = r • x := rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PresheafScalarAction
