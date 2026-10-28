import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramNaturality

/-! # Complex Diagram Map Laws -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramMapLaws.Coordinates

noncomputable section

/-! Functoriality of the original degreewise maps of Čech totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C)
  {P Q S : Cᵒᵖ ⥤ CochainComplex A ℕ} (f : P ⟶ Q) (g : Q ⟶ S)

omit [HasBinaryProducts C] [HasProducts.{0} A] [HasCoproducts.{0} A] in
theorem complexMap_comp : ComplexDiagramNaturality.Coordinates.complexMap (f ≫ g) = ComplexDiagramNaturality.Coordinates.complexMap f ≫ ComplexDiagramNaturality.Coordinates.complexMap g := rfl

omit [Finite ι] in
theorem totalMap_comp : ComplexDiagramNaturality.Coordinates.totalMap U (f ≫ g) = ComplexDiagramNaturality.Coordinates.totalMap U f ≫ ComplexDiagramNaturality.Coordinates.totalMap U g := by
  change (HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)).map
    (((FormalCoproduct.cochainComplexFunctor (NonemptyCechNerve.nerve U)).mapHomologicalComplex (.up ℕ)).map
      (ComplexDiagramNaturality.Coordinates.complexMap (f ≫ g))) = _
  rw [complexMap_comp, Functor.map_comp, Functor.map_comp]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramMapLaws.Coordinates
