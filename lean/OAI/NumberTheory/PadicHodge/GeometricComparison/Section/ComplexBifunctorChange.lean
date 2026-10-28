import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctor

/-! # Complex Bifunctor Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange.SectionComplexBifunctorChange

noncomputable section

/-! A natural section restriction and a map of coefficient complexes
induce the actual natural map of section bifunctors. -/

open _root_.CategoryTheory

universe u v w z r s r' s' t q
variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
  {A : Type r} [Category.{s} A] [Preadditive A]
  {A' : Type r'} [Category.{s'} A'] [Preadditive A']
  {B : Type t} [Category.{q} B] [Preadditive B]
  (T : A ⥤ A') [T.Additive] (S : A ⥤ D ⥤ B) [S.Additive]
  (S' : A' ⥤ D ⥤ B) [S'.Additive]
  (P : C ⥤ CochainComplex A ℕ) (Q : C ⥤ CochainComplex A' ℕ)
  (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q) (b : S ⟶ T ⋙ S')

def complexes : P ⋙ S.mapHomologicalComplex (.up ℕ) ⟶ Q ⋙ S'.mapHomologicalComplex (.up ℕ) :=
  Functor.whiskerLeft P (b.mapHomologicalComplex (.up ℕ)) ≫
    Functor.whiskerRight a (S'.mapHomologicalComplex (.up ℕ))

def rows : ComplexBifunctor.SectionComplexBifunctor.functor S P ⟶ ComplexBifunctor.SectionComplexBifunctor.functor S' Q :=
  (flipFunctor _ _ _).map (Functor.whiskerRight (complexes T S S' P Q a b)
    HomologicalComplex.complexOfFunctorsToFunctorToComplex)

theorem rows_app_f (I : D) (U : C) (i : ℕ) : (((rows T S S' P Q a b).app I).app U).f i =
    (b.app ((P.obj U).X i)).app I ≫ (S'.map ((a.app U).f i)).app I := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.ComplexBifunctorChange.SectionComplexBifunctorChange
