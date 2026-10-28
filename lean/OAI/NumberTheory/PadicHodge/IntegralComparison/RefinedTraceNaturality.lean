import Mathlib.CategoryTheory.Functor.Basic

/-! # Refined Trace Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedTraceNaturality

/-! Compatible traces descend through a literal common refinement. -/

open _root_.CategoryTheory

universe u v w t

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{t} D]

theorem of_factorization (F : C ⥤ D) {A B L : C} {R : D}
    (l : A ⟶ L) (r : B ⟶ L) (f : B ⟶ A)
    (tA : F.obj A ⟶ R) (tB : F.obj B ⟶ R) (tL : F.obj L ⟶ R)
    (hl : F.map l ≫ tL = tA) (hr : F.map r ≫ tL = tB) (hf : f ≫ l = r) :
    F.map f ≫ tA = tB := by
  rw [← hl, ← Category.assoc, ← F.map_comp, hf]
  exact hr

end OAI.NumberTheory.PadicHodge.IntegralComparison.RefinedTraceNaturality
