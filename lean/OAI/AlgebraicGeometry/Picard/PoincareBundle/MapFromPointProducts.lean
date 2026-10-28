import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # Map From Point Products -/

namespace OAI.AlgebraicGeometry.Picard.PoincareBundle.MapFromPointProducts.Group

/-! Multiplicativity on all test objects proves the full group-object homomorphism property. -/

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open scoped _root_.CategoryTheory.MonObj

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {B D : C} [GrpObj B] [GrpObj D] (m : B ⟶ D)
  (hm : ∀ (T : C) (x y : T ⟶ B), (x * y) ≫ m = (x ≫ m) * (y ≫ m))

include hm

/-- The unit follows from multiplicativity because an idempotent in a group is the unit. -/
theorem one_comp (T : C) : (1 : T ⟶ B) ≫ m = 1 := by
  have h : ((1 : T ⟶ B) ≫ m) * 1 = ((1 : T ⟶ B) ≫ m) * ((1 : T ⟶ B) ≫ m) := by
    simpa only [mul_one, one_mul] using hm T 1 1
  exact (mul_left_cancel h).symm

/-- Product preservation on all test objects is the group-scheme homomorphism condition. -/
theorem isMonHom : IsMonHom m := by
  constructor
  · simpa only [MonObj.one_eq_one] using one_comp m hm (𝟙_ C)
  · rw [MonObj.mul_eq_mul, hm]
    simp only [MonObj.mul_eq_mul, MonObj.comp_mul, tensorHom_fst, tensorHom_snd]

end OAI.AlgebraicGeometry.Picard.PoincareBundle.MapFromPointProducts.Group
