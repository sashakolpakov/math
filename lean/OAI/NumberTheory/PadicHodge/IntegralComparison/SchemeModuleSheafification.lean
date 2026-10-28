import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits

/-! # Scheme Module Sheafification -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeModuleSheafification

noncomputable section

/-!
# IntegralComparison: additive sheafification of modules on the original scheme
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

universe u

variable (X : Scheme.{u})

def functor : PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules :=
  PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

instance additive : (functor X).Additive where
  map_add {M N f g} := by
    apply (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map_injective
    exact (PresheafOfModules.toPresheaf.{u} X.ringCatSheaf.obj ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_add (f := f) (g := g)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SchemeModuleSheafification
