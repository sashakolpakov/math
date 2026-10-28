import Mathlib.CategoryTheory.Functor.Basic

/-! # Functor Composition Square -/

namespace OAI.AlgebraicGeometry.ComplexMultiplication.FunctorCompositionSquare

/-! # Mapping an actual source square through two functors -/
open _root_.CategoryTheory
universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]

theorem mapFunctorCompositionSquare (H : C ⥤ D) (F : D ⥤ E)
    {A B : D} {U V W : C} (u : A ⟶ H.obj U) (v : U ⟶ V) (w : V ⟶ W)
    (u' : A ⟶ B) (z : B ⟶ H.obj W)
    (h : u ≫ H.map (v ≫ w) = u' ≫ z) :
    F.map u ≫ F.map (H.map v) ≫ F.map (H.map w) = F.map u' ≫ F.map z := by
  simpa only [Functor.map_comp, Category.assoc] using congrArg F.map h

end OAI.AlgebraicGeometry.ComplexMultiplication.FunctorCompositionSquare
