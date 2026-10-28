import OAI.NumberTheory.PadicHodge.IntegralComparison.BicomplexCoefficientEdge
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison

/-! # Coefficient Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.CoefficientEdge

noncomputable section

/-! The literal zeroth-row edge commutes with additive coefficient
functors and their canonical total-complex comparison. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D] (G : C ⥤ D) [G.Additive]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))
  (A : CochainComplex C ℕ) (a : A ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)

def rowMap : (G.mapHomologicalComplex (.up ℕ)).obj A ⟶
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K).X 0 :=
  (G.mapHomologicalComplex (.up ℕ)).map a

include ha in
omit [HasCoproducts C] [HasCoproducts D] in
theorem closed : rowMap G K A a ≫ (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K).d 0 1 = 0 :=
  ((G.mapHomologicalComplex (.up ℕ)).map_comp a (K.d 0 1)).symm.trans
    ((congrArg (G.mapHomologicalComplex (.up ℕ)).map ha).trans
      ((G.mapHomologicalComplex (.up ℕ)).map_zero _ _))

def edge : (G.mapHomologicalComplex (.up ℕ)).obj A ⟶
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K).total (.up ℕ) :=
  BicomplexCoefficientEdge.edge _ _ (rowMap G K A a) (closed G K A a ha)

theorem comparison : edge G K A a ha ≫ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison G K =
    (G.mapHomologicalComplex (.up ℕ)).map (BicomplexCoefficientEdge.edge K A a ha) := by
  apply HomologicalComplex.Hom.ext
  funext n
  simp only [HomologicalComplex.comp_f, edge, BicomplexCoefficientEdge.component]
  change (G.map (a.f n) ≫ (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K).ιTotal (.up ℕ) 0 n n (Nat.zero_add n)) ≫
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent G K n =
      G.map ((BicomplexCoefficientEdge.edge K A a ha).f n)
  rw [BicomplexCoefficientEdge.component]
  erw [Category.assoc, AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent, ← G.map_comp]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Additive.CoefficientEdge
