import Mathlib.CategoryTheory.Functor.Currying

/-! # Bifunctor Diagonal Eq -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalEq.BifunctorDiagonal

/-! The diagonal of a covariant bifunctor, with either order of
the two component maps made explicit. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A]
  (P : C ⥤ C ⥤ A)

def functor : C ⥤ A := CategoryTheory.Functor.diag C ⋙ CategoryTheory.Functor.uncurry.obj P

theorem map_eq {X Y : C} (f : X ⟶ Y) :
    (functor P).map f = (P.obj X).map f ≫ (P.map f).app Y :=
  ((P.map f).naturality f).symm

end OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalEq.BifunctorDiagonal
