import OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.CoefficientTotal

/-! # Total Functor -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor

noncomputable section

/-! Maps of actual complex-valued diagrams induce the original
assembled Cech total maps functorially. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits Simplicial

universe u v a b
variable {C : Type u} [Category.{v} C]
  {A : Type a} [Category.{b} A] [Abelian A] [HasProducts.{0} A] [HasCoproducts.{0} A]
  (E : SimplicialObject (FormalCoproduct.{0} C))

def functor : (Cᵒᵖ ⥤ CochainComplex A ℕ) ⥤ CochainComplex A ℕ :=
  AlgebraicGeometry.Crystalline.Cohomology.ComplexAssemblyQuasi.ComplexAssembly.functor (.up ℕ) ⋙
    (FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ) ⋙
      HomologicalComplex₂.totalFunctor A (.up ℕ) (.up ℕ) (.up ℕ)

theorem obj (P : Cᵒᵖ ⥤ CochainComplex A ℕ) :
    (functor E).obj P = CoefficientTotal.CechAssemblyCoefficientTotal.total E P := rfl

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.CechAssembly.TotalFunctor.CechAssemblyTotalFunctor
