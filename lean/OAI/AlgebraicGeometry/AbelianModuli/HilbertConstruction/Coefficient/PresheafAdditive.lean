import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.ModulePresheafFunctor
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Presheaf Additive -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PresheafAdditive

noncomputable section

/-! Coefficient-module presheaves depend additively on sheaf morphisms. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

instance coefficientPresheaf_preadditive {X : Scheme.{u}} {R : Type u} [CommRing R] :
    Preadditive (TopCat.Presheaf (ModuleCat.{u} R) X) :=
  inferInstanceAs (Preadditive (X.Opensᵒᵖ ⥤ ModuleCat.{u} R))

instance coefficientModulePresheafFunctor_additive {X : Scheme.{u}} {R : Type u} [CommRing R]
    (c : R →+* Γ(X, ⊤)) : (ModulePresheafFunctor.coefficientModulePresheafFunctor c).Additive where
  map_add := by
    intro M N f g
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    ext x
    rfl

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.PresheafAdditive
