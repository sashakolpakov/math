import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.CategoryTheory.Functor.Currying

/-! # Complex Bifunctor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor

noncomputable section

/-! Applying a presheaf-valued section functor to a diagram of
complexes gives a bifunctor, with the section variable first. -/

open _root_.CategoryTheory

universe u v w z r s t q
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  {A : Type r} [Category.{s} A] [Preadditive A]
  {B : Type t} [Category.{q} B] [Preadditive B]
  (S : A ⥤ D ⥤ B) [S.Additive] (P : C ⥤ CochainComplex A ℕ)

def functor : D ⥤ C ⥤ CochainComplex B ℕ :=
  (P ⋙ S.mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex).flip

def rowIso (I : D) : (functor S P).obj I ≅
    P ⋙ (S ⋙ (evaluation D B).obj I).mapHomologicalComplex (.up ℕ) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

theorem row_map (I : D) {X Y : C} (f : X ⟶ Y) :
    ((functor S P).obj I).map f =
      ((S ⋙ (evaluation D B).obj I).mapHomologicalComplex (.up ℕ)).map (P.map f) := rfl

theorem restriction_f {I J : D} (f : I ⟶ J) (X : C) (n : ℕ) :
    (((functor S P).map f).app X).f n = (S.obj ((P.obj X).X n)).map f := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctor.SectionComplexBifunctor
