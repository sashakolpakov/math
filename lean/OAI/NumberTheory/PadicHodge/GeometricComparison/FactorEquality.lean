import Mathlib.CategoryTheory.Category.Basic

/-! # Factor Equality -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.FactorEquality.ComparisonFactorEquality

/-! Equal comparison factors determine the same original composite. -/

open _root_.CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

theorem equality {A B D : C} (f g : A ⟶ D) (a a' : A ⟶ B) (b b' : B ⟶ D)
    (hf : f = a ≫ b) (hg : g = a' ≫ b') (ha : a = a') (hb : b = b') : f = g := by
  rw [hf, hg, ha, hb]

end OAI.NumberTheory.PadicHodge.GeometricComparison.FactorEquality.ComparisonFactorEquality
