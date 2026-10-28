import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramMapLaws

/-! # Complex Diagram Iso -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramIso.Coordinates

noncomputable section

/-! A genuine isomorphism of complex-valued diagrams induces the
corresponding isomorphism of their original degreewise Čech totals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C)
  {P Q : Cᵒᵖ ⥤ CochainComplex A ℕ} (e : P ≅ Q)

omit [HasBinaryProducts C] [HasProducts.{0} A] [HasCoproducts.{0} A] in
def complexIso : ComplexDiagramCoordinates.complex P ≅ ComplexDiagramCoordinates.complex Q where
  hom := ComplexDiagramNaturality.Coordinates.complexMap e.hom
  inv := ComplexDiagramNaturality.Coordinates.complexMap e.inv
  hom_inv_id := by
    rw [← ComplexDiagramMapLaws.Coordinates.complexMap_comp, e.hom_inv_id]
    rfl
  inv_hom_id := by
    rw [← ComplexDiagramMapLaws.Coordinates.complexMap_comp, e.inv_hom_id]
    rfl

def degreewiseTotalIso :
    (CechCoefficient.Total.bicomplex (NonemptyCechNerve.nerve U) (ComplexDiagramCoordinates.complex P)).total (.up ℕ) ≅
    (CechCoefficient.Total.bicomplex (NonemptyCechNerve.nerve U) (ComplexDiagramCoordinates.complex Q)).total (.up ℕ) :=
  HomologicalComplex₂.total.mapIso
    (((FormalCoproduct.cochainComplexFunctor (NonemptyCechNerve.nerve U)).mapHomologicalComplex
      (.up ℕ)).mapIso (complexIso e)) (.up ℕ)

omit [Finite ι] in
theorem degreewiseTotalIso_hom : (degreewiseTotalIso U e).hom = ComplexDiagramNaturality.Coordinates.totalMap U e.hom := rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramIso.Coordinates
