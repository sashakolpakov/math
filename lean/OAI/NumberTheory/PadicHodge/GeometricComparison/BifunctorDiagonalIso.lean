import OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalEq

/-! # Bifunctor Diagonal Iso -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalIso.BifunctorDiagonalFlip

/-! Interchanging the two variables gives a canonical identity-component
isomorphism on a bifunctor diagonal. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A]
  (P : C ⥤ C ⥤ A)

def iso : BifunctorDiagonalEq.BifunctorDiagonal.functor P ≅ BifunctorDiagonalEq.BifunctorDiagonal.functor P.flip :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    exact (Category.comp_id _).trans
      (((P.map f).naturality f).symm.trans (Category.id_comp _).symm))

end OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalIso.BifunctorDiagonalFlip
