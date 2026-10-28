import Mathlib.CategoryTheory.Functor.Basic

/-! # Mapped Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.MappedSquare.MappedSquareCoordinates

/-! A functor carries a commuting square to any checked coordinates
for its four arrows. -/

open _root_.CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
  {W X Y Z : C} (a : W ⟶ X) (b : X ⟶ Z) (c : W ⟶ Y) (d : Y ⟶ Z)
  (a' : F.obj W ⟶ F.obj X) (b' : F.obj X ⟶ F.obj Z)
  (c' : F.obj W ⟶ F.obj Y) (d' : F.obj Y ⟶ F.obj Z)

theorem square (h : a ≫ b = c ≫ d)
    (ha : F.map a = a') (hb : F.map b = b')
    (hc : F.map c = c') (hd : F.map d = d') : a' ≫ b' = c' ≫ d' := by
  rw [← ha, ← hb, ← hc, ← hd, ← F.map_comp, h, F.map_comp]

end OAI.NumberTheory.PadicHodge.GeometricComparison.MappedSquare.MappedSquareCoordinates
