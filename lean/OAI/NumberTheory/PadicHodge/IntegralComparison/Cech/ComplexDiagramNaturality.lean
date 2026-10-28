import OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramCoordinates
import OAI.NumberTheory.PadicHodge.GeometricComparison.CechCone.CoefficientNaturality

/-! # Complex Diagram Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramNaturality.Coordinates

noncomputable section

/-! The exact change from complex-valued to degreewise Čech coordinates
is natural for maps of the original diagrams. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite

universe u v w z
variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]
  {A : Type w} [Category.{z} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  {ι : Type} [Finite ι] (U : ι → C) {P Q : Cᵒᵖ ⥤ CochainComplex A ℕ} (α : P ⟶ Q)

local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve U

def complexMap : ComplexDiagramCoordinates.complex P ⟶ ComplexDiagramCoordinates.complex Q where
  f n := Functor.whiskerRight α (HomologicalComplex.eval A (.up ℕ) n)
  comm' i j _ := by
    apply NatTrans.ext
    funext V
    exact (α.app V).comm i j

def bicomplexMap : CechCoefficient.Total.bicomplex N (ComplexDiagramCoordinates.complex P) ⟶
    CechCoefficient.Total.bicomplex N (ComplexDiagramCoordinates.complex Q) :=
  ((FormalCoproduct.cochainComplexFunctor N).mapHomologicalComplex (.up ℕ)).map (complexMap α)

def totalMap := HomologicalComplex₂.total.map (bicomplexMap U α) (.up ℕ)

omit [HasCoproducts A] in
theorem bicomplex_natural : GeometricComparison.CechCone.CoefficientNaturality.CechConeCoefficientNaturality.bicomplexMap U α ≫
    (ComplexDiagramCoordinates.bicomplexIso U Q).hom = (ComplexDiagramCoordinates.bicomplexIso U P).hom ≫ bicomplexMap U α := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact GeometricComparison.Finite.CechCoefficientChange.FiniteCechCoefficientChange.naturality (HomologicalComplex.eval A (.up ℕ) i)
    N (fun _ => inferInstanceAs (Finite (Fin _ → ι))) α

theorem total_natural : (GeometricComparison.CechCone.TotalFunctor.CechConeTotalFunctor.functor U).map α ≫
    (ComplexDiagramCoordinates.totalIso U Q).hom = (ComplexDiagramCoordinates.totalIso U P).hom ≫ totalMap U α := by
  let T := HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)
  exact (T.map_comp (GeometricComparison.CechCone.CoefficientNaturality.CechConeCoefficientNaturality.bicomplexMap U α)
    (ComplexDiagramCoordinates.bicomplexIso U Q).hom).symm.trans
      ((congrArg T.map (bicomplex_natural U α)).trans
        (T.map_comp (ComplexDiagramCoordinates.bicomplexIso U P).hom (bicomplexMap U α)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Cech.ComplexDiagramNaturality.Coordinates
