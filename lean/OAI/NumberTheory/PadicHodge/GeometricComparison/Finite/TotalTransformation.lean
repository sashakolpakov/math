import OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalIso

/-! # Total Transformation -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalTransformation.FiniteTotalTransformation

noncomputable section

/-! Finite total comparison is natural in an actual transformation between additive coefficient functors. -/

open _root_.CategoryTheory Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasFiniteCoproducts C] [HasFiniteCoproducts D]
  {F G : C ⥤ D} [F.Additive] [G.Additive] (a : F ⟶ G)

local instance (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K
local instance (K : HomologicalComplex₂ D (.up ℕ) (.up ℕ)) : K.HasTotal (.up ℕ) :=
  AlgebraicGeometry.Comparison.Betti.TotalExists.hasTotal_of_finiteCoproducts K

def bicomplexMap (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K ⟶ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K :=
  (NatTrans.mapHomologicalComplex (NatTrans.mapHomologicalComplex a (.up ℕ)) (.up ℕ)).app K

theorem naturality (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    total.map (bicomplexMap a K) (.up ℕ) ≫ (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso G K).hom =
      (AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonIso F K).hom ≫
        (NatTrans.mapHomologicalComplex a (.up ℕ)).app (K.total (.up ℕ)) := by
  ext n : 1
  apply total.hom_ext
  intro q p h
  change (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      (total.map (bicomplexMap a K) (.up ℕ)).f n ≫ AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonComponent G K n =
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.finiteTotalComparisonComponent F K n ≫ a.app ((K.total (.up ℕ)).X n)
  rw [← Category.assoc, ιTotal_map, Category.assoc, AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent,
    ← Category.assoc, AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor.ι_finiteTotalComparisonComponent]
  exact (a.naturality (K.ιTotal (.up ℕ) q p n h)).symm

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.Finite.TotalTransformation.FiniteTotalTransformation
