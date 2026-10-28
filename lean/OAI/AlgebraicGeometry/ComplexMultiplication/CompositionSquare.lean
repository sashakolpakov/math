import Mathlib.CategoryTheory.Category.Basic

/-! # Composition Square -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.CompositionSquare

/-! # Composition of an actual commuting square with two further maps -/

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C]

theorem compositionSquare_postcomp {A B D E F G H : C}
    (u : A ⟶ B) (v : B ⟶ D) (w : D ⟶ E) (u' : A ⟶ F) (v' : F ⟶ E)
    (b : E ⟶ G) (a : G ⟶ H) (h : u ≫ v ≫ w = u' ≫ v') :
    u ≫ (v ≫ w ≫ b) ≫ a = u' ≫ v' ≫ b ≫ a := by
  calc
    _ = (u ≫ v ≫ w) ≫ b ≫ a := by simp only [Category.assoc]
    _ = (u' ≫ v') ≫ b ≫ a := congrArg (fun f => f ≫ b ≫ a) h
    _ = _ := by rw [Category.assoc]

end OAI.AlgebraicGeometry.ComplexMultiplication.CompositionSquare
