import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CategoryProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-! # Category Has Ext -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CategoryHasExt

/-!

# HasExt instance for Module Category

If we assume `Small.{v} R`, the category `ModuleCat.{v} R` has enough projectives, which allows to
introduce the instance `HasExt.{v} (ModuleCat.{v} R)`. As a result, `Ext`-groups in this category
of modules are defined and belong to `Type v`.

-/

/- HilbertConstruction-local adaptation, using default elaboration settings. -/

universe v u

variable (R : Type u) [Ring R]

instance [Small.{v} R] : CategoryTheory.HasExt.{v} (ModuleCat.{v} R) :=
  CategoryTheory.hasExt_of_enoughProjectives.{v} (ModuleCat.{v} R)

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.CategoryHasExt
