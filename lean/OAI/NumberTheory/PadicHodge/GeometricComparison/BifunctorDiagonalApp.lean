import OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalEq

/-! # Bifunctor Diagonal App -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalApp.BifunctorDiagonalMap

/-! Natural maps of bifunctors induce their actual diagonal maps. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A]
  {P Q : C ⥤ C ⥤ A} (a : P ⟶ Q)

def map : BifunctorDiagonalEq.BifunctorDiagonal.functor P ⟶ BifunctorDiagonalEq.BifunctorDiagonal.functor Q :=
  Functor.whiskerLeft (Functor.diag C) (Functor.uncurry.map a)

theorem app (U : C) : (BifunctorDiagonalMap.map a).app U = (a.app U).app U := rfl

end OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalApp.BifunctorDiagonalMap
