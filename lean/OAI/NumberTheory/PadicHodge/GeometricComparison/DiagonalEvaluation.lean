import OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalEq

/-! # Diagonal Evaluation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.DiagonalEvaluation.DiagonalEvaluationMap

/-! Evaluating a natural family of cones on its matching index
gives a natural map to the bifunctor diagonal. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A]
  (D : C ⥤ A) (P : C ⥤ C ⥤ A)
  (a : D ⋙ Functor.const C ⟶ P)

def transformation : D ⟶ BifunctorDiagonalEq.BifunctorDiagonal.functor P where
  app I := (a.app I).app I
  naturality I J f := by
    have ha := congrArg (fun η => η.app I) (a.naturality f)
    have hb := (a.app J).naturality f
    change D.map f ≫ (a.app J).app J = (a.app I).app I ≫
      ((P.map f).app I ≫ (P.obj J).map f)
    exact (congrArg (fun t => D.map f ≫ t) ((Category.id_comp _).symm.trans hb)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ (P.obj J).map f) ha).trans (Category.assoc _ _ _)))

end OAI.NumberTheory.PadicHodge.GeometricComparison.DiagonalEvaluation.DiagonalEvaluationMap
