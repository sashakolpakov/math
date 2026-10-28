import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexEvaluated

/-! # Constant Complex F -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexF.ConstantComplexDiagonalCoordinates

noncomputable section

/-! The canonical diagonal evaluation retains the original degreewise section maps. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A] [Preadditive A]
  (D : C ⥤ CochainComplex A ℕ) (P : C ⥤ CochainComplex (C ⥤ A) ℕ)

local instance constPreservesZero : (Functor.const C : A ⥤ C ⥤ A).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable (a : D ⋙ (Functor.const C : A ⥤ C ⥤ A).mapHomologicalComplex (.up ℕ) ⟶ P)

theorem app (X : C) : (ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation D P a).app X =
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map (a.app X)).app X :=
  Category.comp_id _

theorem app_f (X : C) (n : ℕ) : ((ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation D P a).app X).f n =
    ((a.app X).f n).app X := congrArg (fun a => a.f n) (ConstantComplexDiagonalCoordinates.app D P a X)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexF.ConstantComplexDiagonalCoordinates
