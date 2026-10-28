import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalConeChange
import OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCech
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalFunctorSquare
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.TotalSquare

/-! # Diagonal Cech Change -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechChange.SectionDiagonalCechChange

noncomputable section

/-! The actual diagonal-section to Cech-section comparison commutes with
a section restriction and a map of coefficient-complex diagrams. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w v' w' z t
variable (C : Type u) [SemilatticeInf C]
  {A : Type v} [Category.{w} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {A' : Type v'} [Category.{w'} A'] [Abelian A'] [HasProducts.{0} A'] [HasCoproducts.{0} A']
  (R : Type z) [CommRing R] (T : A ⥤ A') [T.Additive]
  (S : A ⥤ Cᵒᵖ ⥤ ModuleCat.{max z t} R) [S.Additive]
  (S' : A' ⥤ Cᵒᵖ ⥤ ModuleCat.{max z t} R) [S'.Additive]
  (P : Cᵒᵖ ⥤ CochainComplex A ℕ) (Q : Cᵒᵖ ⥤ CochainComplex A' ℕ)
  (a : P ⋙ T.mapHomologicalComplex (.up ℕ) ⟶ Q) (b : S ⟶ T ⋙ S')
  (hP : ∀ I V : C, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor S P).obj (op I)).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  (hQ : ∀ I V : C, IsIso (((ComplexBifunctor.SectionComplexBifunctor.functor S' Q).obj (op I)).map
    (homOfLE (inf_le_left : V ⊓ I ≤ V)).op))
  {ι : Type} [Finite ι] (U : ι → C)

theorem natural : DiagonalCech.SectionDiagonalCechComparison.map C R S P hP U ≫
    CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.map T S S' U P Q a b =
      DiagonalConeChange.SectionDiagonalConeChange.diagonalMap C T S S' P Q a b ≫
        DiagonalCech.SectionDiagonalCechComparison.map C R S' Q hQ U := by
  let α := ComplexBifunctorChange.SectionComplexBifunctorChange.complexes T S S' P Q a b
  have hInv := IntegralComparison.InverseCoordinateHomology.inverse
    (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso S U P) (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso S' U Q)
    (CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.map T S S' U P Q a b) ((CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map α)
    (CechCone.TotalFunctorSquare.CechConeTotalFunctorSquare.natural T S S' U P Q a b)
  have hAug := CechCone.TotalSquare.CechConeTotalConeSquare.natural U (DiagonalCone.SectionDiagonalCone.cone C S P hP)
    (DiagonalCone.SectionDiagonalCone.cone C S' Q hQ) α (DiagonalConeChange.SectionDiagonalConeChange.diagonalMap C T S S' P Q a b)
    (DiagonalConeChange.SectionDiagonalConeChange.cone C T S S' P Q a b hP hQ)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => CechCone.Total.CechConeTotal.augmentation U _ _ (DiagonalCone.SectionDiagonalCone.cone C S P hP) ≫ q) hInv.symm).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun q => q ≫ (CechCone.TotalCoefficient.CechConeTotalCoefficient.totalIso S' U Q).inv) hAug).trans
          (Category.assoc _ _ _))))

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Section.DiagonalCechChange.SectionDiagonalCechChange
