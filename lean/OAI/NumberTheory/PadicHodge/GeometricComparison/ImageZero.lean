import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms

/-! # Image Zero -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ImageZero.ComparisonImageZero

/-! A commuting target square and a factored source image preserve
vanishing under a specified comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]

theorem transfer {H A B D : C} (i : H ⟶ A) (a : A ⟶ B)
    (b : B ⟶ B) (e : B ⟶ D) (c : D ⟶ D)
    (h : i ≫ a ≫ b = 0) (he : b ≫ e = e ≫ c) : i ≫ (a ≫ e) ≫ c = 0 := by
  rw [Category.assoc, ← he, ← Category.assoc a, ← Category.assoc i, h, zero_comp]

theorem factor {H A B T D E : C} (i : H ⟶ A) (r : A ⟶ B)
    (a : B ⟶ D) (t : H ⟶ T) (j : T ⟶ D) (b : D ⟶ E)
    (h : i ≫ r ≫ a = t ≫ j) (hj : j ≫ b = 0) : i ≫ r ≫ a ≫ b = 0 := by
  rw [← Category.assoc r, ← Category.assoc i, h, Category.assoc, hj, comp_zero]

end OAI.NumberTheory.PadicHodge.GeometricComparison.ImageZero.ComparisonImageZero
