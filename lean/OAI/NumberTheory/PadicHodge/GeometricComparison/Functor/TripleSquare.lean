import Mathlib.CategoryTheory.Functor.Basic

/-! # Triple Square -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.TripleSquare.FunctorTripleSquare

/-! A functor preserves an actual square with three successive
maps on one side. -/

open _root_.CategoryTheory

universe u v a b
variable {C : Type u} [Category.{v} C] {D : Type a} [Category.{b} D]
  (F : C ⥤ D) {A B E G H : C}
  (a : A ⟶ B) (b : B ⟶ E) (c : E ⟶ G) (d : A ⟶ H) (e : H ⟶ G)
  (h : a ≫ b ≫ c = d ≫ e)

include h in
theorem square : F.map a ≫ F.map b ≫ F.map c = F.map d ≫ F.map e := by
  rw [← F.map_comp, ← F.map_comp, h, F.map_comp]

end OAI.NumberTheory.PadicHodge.GeometricComparison.Functor.TripleSquare.FunctorTripleSquare
