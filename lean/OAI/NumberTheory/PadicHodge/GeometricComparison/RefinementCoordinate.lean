import Mathlib.CategoryTheory.Category.Basic

/-! # Refinement Coordinate -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.RefinementCoordinate.RefinementCoordinateSquare

/-! Assemble a refined comparison square from the three actual
coordinate identities, without unfolding its complexes. -/

open _root_.CategoryTheory

universe u v
variable {C : Type u} [Category.{v} C] {A B D E F G : C}
  (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : B ⟶ F)
  (e : A ⟶ G) (f : G ⟶ F) (g : F ⟶ E) (k : G ⟶ E)
  (h₁ : b ≫ c = d ≫ g) (h₂ : a ≫ d = e ≫ f) (h₃ : f ≫ g = k)

include h₁ h₂ h₃ in
theorem square : a ≫ b ≫ c = e ≫ k := by
  rw [h₁, ← Category.assoc, h₂, Category.assoc, h₃]

end OAI.NumberTheory.PadicHodge.GeometricComparison.RefinementCoordinate.RefinementCoordinateSquare
