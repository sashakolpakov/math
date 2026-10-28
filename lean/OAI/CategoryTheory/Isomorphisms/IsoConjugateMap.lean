import Mathlib.CategoryTheory.Functor.Category

/-! # Iso Conjugate Map -/

namespace OAI.CategoryTheory.Isomorphisms.IsoConjugateMap

noncomputable section

open _root_.CategoryTheory
universe u v
def isoConjugateMap {C : Type u} [Category.{v} C]
    {X X' Y Y' : C} (e : X ≅ X') (d : Y ≅ Y') (p : X ⟶ Y) : X' ⟶ Y' :=
  e.inv ≫ p ≫ d.hom

theorem isoConjugateMap_eq {C : Type u} [Category.{v} C]
    {X X' Y Y' : C} (e : X ≅ X') (d : Y ≅ Y') (p : X ⟶ Y) :
    isoConjugateMap e d p = e.inv ≫ p ≫ d.hom := rfl

end

end OAI.CategoryTheory.Isomorphisms.IsoConjugateMap
