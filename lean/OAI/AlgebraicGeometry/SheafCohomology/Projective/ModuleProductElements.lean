import Mathlib.Algebra.Category.ModuleCat.Products

/-! # Module Product Elements -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleProductElements

/-! Concrete elements of a module product are determined by their categorical projections. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits
universe u v w
variable {R : Type u} [Ring R] {ι : Type v}
    (Z : ι → ModuleCat.{max v w} R) [HasProduct Z]

theorem moduleProductElement_ext {x y : (∏ᶜ Z : ModuleCat.{max v w} R)}
    (h : ∀ i, Pi.π Z i x = Pi.π Z i y) : x = y := by
  apply (ModuleCat.piIsoPi Z).toLinearEquiv.injective
  funext i
  exact (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype Z i) x).trans
    ((h i).trans (ConcreteCategory.congr_hom (ModuleCat.piIsoPi_hom_ker_subtype Z i) y).symm)

end OAI.AlgebraicGeometry.SheafCohomology.Projective.ModuleProductElements
