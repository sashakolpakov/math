import OAI.NumberTheory.PadicHodge.GeometricComparison.TotalCoefficientComposition
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison

/-! # Total Coefficient -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.TotalCoefficient.TotalCoefficientIsoComposition

noncomputable section

/-! The finite total/coefficient isomorphisms, including their inverses,
respect composition of additive coefficient functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D] [HasCoproducts.{0} E]
  (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

theorem iso : AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso (F ⋙ G) K =
    AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K) ≪≫
      (G.mapHomologicalComplex (.up ℕ)).mapIso (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F K) :=
  Iso.ext (TotalCoefficientComposition.TotalCoefficientComparisonComposition.comparison F G K)

theorem inv : (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso (F ⋙ G) K).inv =
    (G.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso F K).inv ≫
      (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)).inv :=
  congrArg Iso.inv (iso F G K)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.TotalCoefficient.TotalCoefficientIsoComposition
