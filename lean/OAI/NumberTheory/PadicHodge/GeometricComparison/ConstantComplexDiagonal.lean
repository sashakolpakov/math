import OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexEvaluated
import OAI.NumberTheory.PadicHodge.GeometricComparison.BifunctorDiagonalApp

/-! # Constant Complex Diagonal -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexDiagonal.ConstantComplexDiagonalNaturality

noncomputable section

/-! Diagonal evaluation preserves a commutative square of constant-source
maps of presheaf complexes. -/

open _root_.CategoryTheory

universe u v w z
variable {C : Type u} [Category.{v} C] {A : Type w} [Category.{z} A] [Preadditive A]
  (D D' : C ⥤ CochainComplex A ℕ) (P P' : C ⥤ CochainComplex (C ⥤ A) ℕ)

local instance constPreservesZero : (Functor.const C : A ⥤ C ⥤ A).PreservesZeroMorphisms where
  map_zero _ _ := rfl

variable
  (a : D ⋙ (Functor.const C : A ⥤ C ⥤ A).mapHomologicalComplex (.up ℕ) ⟶ P)
  (a' : D' ⋙ (Functor.const C : A ⥤ C ⥤ A).mapHomologicalComplex (.up ℕ) ⟶ P')
  (d : D ⟶ D') (b : P ⟶ P')
  (h : a ≫ b = Functor.whiskerRight d ((Functor.const C : A ⥤ C ⥤ A).mapHomologicalComplex (.up ℕ)) ≫ a')

def diagonalMap := BifunctorDiagonalApp.BifunctorDiagonalMap.map
  ((flipFunctor _ _ _).map (Functor.whiskerRight b HomologicalComplex.complexOfFunctorsToFunctorToComplex))

include h in
theorem transformation : ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation D P a ≫ diagonalMap P P' b =
    d ≫ ConstantComplexEvaluated.ConstantComplexDiagonalMap.transformation D' P' a' := by
  apply NatTrans.ext
  funext I
  apply HomologicalComplex.Hom.ext
  funext i
  have hi := congrArg (fun q => ((q.app I).f i).app I) h
  change ((a.app I).f i).app I ≫ ((b.app I).f i).app I =
    (d.app I).f i ≫ ((a'.app I).f i).app I at hi
  change ((((a.app I).f i).app I ≫ 𝟙 _) ≫ ((b.app I).f i).app I) =
    (d.app I).f i ≫ (((a'.app I).f i).app I ≫ 𝟙 _)
  exact (congrArg (fun q => q ≫ ((b.app I).f i).app I)
    (Category.comp_id (((a.app I).f i).app I))).trans
      (hi.trans (congrArg (fun q => (d.app I).f i ≫ q)
        (Category.comp_id (((a'.app I).f i).app I)).symm))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.ConstantComplexDiagonal.ConstantComplexDiagonalNaturality
