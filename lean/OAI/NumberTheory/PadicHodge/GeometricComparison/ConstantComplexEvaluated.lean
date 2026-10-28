import OAI.NumberTheory.PadicHodge.GeometricComparison.DiagonalEvaluation
import OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalIso
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Constant Complex Evaluated -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexEvaluated.ConstantComplexDiagonalMap

noncomputable section

/-! A natural constant-source map of presheaf complexes evaluates
canonically to the section bifunctor diagonal. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A] [Preadditive A]
  (D : C ⥤ CochainComplex A ℕ) (P : C ⥤ CochainComplex (C ⥤ A) ℕ)

local instance constPreservesZero : (Functor.const C : A ⥤ C ⥤ A).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable
  (a : D ⋙ (Functor.const C : A ⥤ C ⥤ A).mapHomologicalComplex (.up ℕ) ⟶ P)

def evaluated : D ⋙ Functor.const C ⟶ P ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex :=
  Functor.whiskerRight a HomologicalComplex.complexOfFunctorsToFunctorToComplex

def transformation : D ⟶ BifunctorDiagonalEq.BifunctorDiagonal.functor
    (P ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex).flip :=
  DiagonalEvaluation.DiagonalEvaluationMap.transformation D _ (evaluated D P a) ≫
    (BifunctorDiagonalIso.BifunctorDiagonalFlip.iso (P ⋙ HomologicalComplex.complexOfFunctorsToFunctorToComplex)).hom

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexEvaluated.ConstantComplexDiagonalMap
