import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso

/-! # Inverse -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.Inverse.FunctorInverseComparison

/-! Cancellation of an explicitly specified comparison isomorphism
preserves a global comparison whose two factors are already identified. -/
open _root_.CategoryTheory
universe u v a b
variable {C : Type u} [Category.{v} C] {D : Type a} [Category.{b} D]
  (F : C ⥤ D) {K L M : C} {B : D}
  (g : K ⟶ M) (e : L ≅ M)
  (a : F.obj K ⟶ B) (b : F.obj M ⟶ B) (c : F.obj L ⟶ B)

theorem equality (hg : F.map g ≫ b = a) (he : F.map e.hom ≫ b = c) :
    F.map (g ≫ e.inv) ≫ c = a := by
  rw [← he, ← Category.assoc, ← F.map_comp, Category.assoc,
    e.inv_hom_id, Category.comp_id]
  exact hg

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.Inverse.FunctorInverseComparison
