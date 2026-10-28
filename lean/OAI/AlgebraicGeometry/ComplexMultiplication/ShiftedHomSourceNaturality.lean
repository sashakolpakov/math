import Mathlib.CategoryTheory.Shift.ShiftedHom

/-! # Shifted Hom Source Naturality -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedHomSourceNaturality

noncomputable section

/-! # Source transport for actual shifted morphisms -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
  [HasShift C ℤ] [HasShift D ℤ]

/-- A genuine source square commutes after shifted functorial mapping and target transport. -/
theorem shiftedHomSourceNaturality (G : C ⥤ D) [G.CommShift ℤ]
    {A B K : C} {S T L : D} (a : S ⟶ G.obj A) (b : S ⟶ T)
    (k : T ⟶ G.obj B) (t : G.obj K ⟶ L) (g : A ⟶ B)
    (h : a ≫ G.map g = b ≫ k) (n : ℤ) (z : ShiftedHom B K n) :
    (ShiftedHom.mk₀ 0 rfl a).comp
        ((((ShiftedHom.mk₀ 0 rfl g).comp z (add_zero n)).map G).comp
          (ShiftedHom.mk₀ 0 rfl t) (zero_add n)) (add_zero n) =
      (ShiftedHom.mk₀ 0 rfl b).comp
        ((ShiftedHom.mk₀ 0 rfl k).comp
          ((z.map G).comp (ShiftedHom.mk₀ 0 rfl t) (zero_add n))
            (add_zero n)) (add_zero n) := by
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map,
    Functor.map_comp, Category.assoc]
  rw [← Category.assoc a (G.map g), h, Category.assoc]

end

end OAI.AlgebraicGeometry.ComplexMultiplication.ShiftedHomSourceNaturality
