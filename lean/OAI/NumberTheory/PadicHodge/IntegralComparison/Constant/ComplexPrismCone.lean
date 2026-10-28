import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexEvaluated

/-! # Complex Prism Cone -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.ComplexPrismCone

noncomputable section

/-! A genuine constant-source map of complexes gives the prism cone
on the corresponding section bifunctor. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A] [Preadditive A]
  (Q : C ⥤ CochainComplex A ℕ) (P : C ⥤ CochainComplex (C ⥤ A) ℕ)
local instance constZero : (Functor.const C : A ⥤ C ⥤ A).PreservesZeroMorphisms where
  map_zero _ _ := rfl
variable (a : Q ⋙ (Functor.const C : A ⥤ C ⥤ A).mapHomologicalComplex (.up ℕ) ⟶ P)

def cone : (Functor.const C).obj Q ⟶
    (P ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex).flip :=
  (CategoryTheory.flipFunctor C C (CochainComplex A ℕ)).map
    (GeometricComparison.ConstantComplexEvaluated.ConstantComplexDiagonalMap.evaluated Q P a)

theorem component (V I : C) (r : ℕ) : (((cone Q P a).app I).app V).f r =
    ((a.app V).f r).app I := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Constant.ComplexPrismCone
