import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor

/-! # Total Coefficient Composition -/

namespace OAI

noncomputable section

namespace NumberTheory.PadicHodge.GeometricComparison.TotalCoefficientComposition.TotalCoefficientComparisonNaturality

/-! The original total/coefficient comparison is natural in bicomplex
maps and in transformations of additive coefficient functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D]
  (F : C ⥤ D) [F.Additive]
  {K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} (a : K ⟶ L)

def bicomplexMap : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K ⟶ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F L :=
  ((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).map a

theorem natural : HomologicalComplex₂.total.map (bicomplexMap F a) (.up ℕ) ≫ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F L =
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F K ≫ (F.mapHomologicalComplex (.up ℕ)).map (HomologicalComplex₂.total.map a (.up ℕ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro q p h
  change (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      ((HomologicalComplex₂.total.map (bicomplexMap F a) (.up ℕ)).f n ≫ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent F L n) =
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent F K n ≫ F.map ((HomologicalComplex₂.total.map a (.up ℕ)).f n))
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc, AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent,
    ← Category.assoc, AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent]
  change F.map ((a.f q).f p) ≫ F.map (L.ιTotal (.up ℕ) q p n h) =
    F.map (K.ιTotal (.up ℕ) q p n h) ≫ F.map ((HomologicalComplex₂.total.map a (.up ℕ)).f n)
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (HomologicalComplex₂.ιTotal_map K L a (.up ℕ) q p n h).symm).trans (F.map_comp _ _))

variable (G : C ⥤ D) [G.Additive] (α : F ⟶ G) (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

def coefficientMap : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K ⟶ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G K :=
  ((α.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).app K

theorem coefficients : HomologicalComplex₂.total.map (coefficientMap F G α K) (.up ℕ) ≫ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison G K =
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F K ≫ (α.mapHomologicalComplex (.up ℕ)).app (K.total (.up ℕ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro q p h
  change (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      ((HomologicalComplex₂.total.map (coefficientMap F G α K) (.up ℕ)).f n ≫ AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent G K n) =
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent F K n ≫ α.app ((K.total (.up ℕ)).X n))
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc, AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent,
    ← Category.assoc, AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent]
  exact (α.naturality (K.ιTotal (.up ℕ) q p n h)).symm

end NumberTheory.PadicHodge.GeometricComparison.TotalCoefficientComposition.TotalCoefficientComparisonNaturality

namespace NumberTheory.PadicHodge.GeometricComparison.TotalCoefficientComposition.TotalCoefficientComparisonComposition

/-! The original total/coefficient comparison respects composition of
additive coefficient functors. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D] [HasCoproducts.{0} E]
  (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

theorem comparison : AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison (F ⋙ G) K =
    AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K) ≫
      (G.mapHomologicalComplex (.up ℕ)).map (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparison F K) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro q p h
  change (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex (F ⋙ G) K).ιTotal (.up ℕ) q p n h ≫
      AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent (F ⋙ G) K n =
    (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K)).ιTotal (.up ℕ) q p n h ≫
      (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent G (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.mapBicomplex F K) n ≫
        G.map (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.totalComparisonComponent F K n))
  rw [AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent, ← Category.assoc, AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent]
  exact (congrArg G.map (AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor.ι_totalComparisonComponent F K q p n h)).symm.trans (G.map_comp _ _)

end NumberTheory.PadicHodge.GeometricComparison.TotalCoefficientComposition.TotalCoefficientComparisonComposition

end

end OAI
