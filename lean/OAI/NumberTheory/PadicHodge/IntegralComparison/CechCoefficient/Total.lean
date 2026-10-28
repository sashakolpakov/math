import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CochainLimits
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison

/-! # Total -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total

noncomputable section

/-! Canonical coefficient change for the actual Čech total complex. -/

open _root_.CategoryTheory Limits

universe w uC vC uA vA uB vB

variable {C : Type uC} [Category.{vC} C]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{w} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{w, w} G]
  (E : SimplicialObject (FormalCoproduct.{w} C))
  (M : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

def bicomplex : HomologicalComplex₂ A (.up ℕ) (.up ℕ) :=
  ((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).obj M

def mappedComplex : CochainComplex (Cᵒᵖ ⥤ B) ℕ :=
  (((Functor.whiskeringRight Cᵒᵖ A B).obj G).mapHomologicalComplex (.up ℕ)).obj M

variable [HasCoproducts.{0} A] [HasCoproducts.{0} B]

def bicomplexIso :
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G (bicomplex E M) ≅ bicomplex E (mappedComplex G M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChange.CechCoefficientChange.complexIso G E (M.X n))
    (fun n m _ => (AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.naturality G E (M.d n m)).symm)

def totalIso [HasFiniteBiproducts A] :
    (G.mapHomologicalComplex (.up ℕ)).obj ((bicomplex E M).total (.up ℕ)) ≅
      (bicomplex E (mappedComplex G M)).total (.up ℕ) :=
  (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (bicomplex E M)).symm ≪≫
    HomologicalComplex₂.total.mapIso (bicomplexIso G E M) (.up ℕ)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total
