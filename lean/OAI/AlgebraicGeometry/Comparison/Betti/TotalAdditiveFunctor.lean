import OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor
import OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalDiagonal

/-! # Total Additive Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor

noncomputable section

section

/-! Additive functors commute with first-quadrant total complexes through finite diagonals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D] (F : C ⥤ D) [F.Additive]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

instance totalComparisonComponent_isIso_of_additive (n : ℕ) :
    IsIso (TotalComplexFunctor.totalComparisonComponent F K n) := by
  have : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) := by
    change Finite {p : ℕ × ℕ // p.1 + p.2 = n}
    exact Betti.Finite.TotalDiagonal.finiteTotalDiagonal n
  exact inferInstanceAs (IsIso (sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)))

def totalComparisonIsoOfAdditive :
    (TotalComplexFunctor.mapBicomplex F K).total (.up ℕ) ≅
      (F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) := by
  have (n : ℕ) : IsIso ((TotalComplexFunctor.totalComparison F K).f n) :=
    totalComparisonComponent_isIso_of_additive F K n
  have : IsIso (TotalComplexFunctor.totalComparison F K) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (TotalComplexFunctor.totalComparison F K)

end

/-! Totalization commutes with actual bicomplex maps under an additive functor. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D] (F : C ⥤ D) [F.Additive]
  {K L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)} (φ : K ⟶ L)

def mapBicomplexMap : TotalComplexFunctor.mapBicomplex F K ⟶ TotalComplexFunctor.mapBicomplex F L :=
  ((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).map φ

theorem totalComparison_naturality :
    total.map (mapBicomplexMap F φ) (.up ℕ) ≫ TotalComplexFunctor.totalComparison F L =
      TotalComplexFunctor.totalComparison F K ≫ (F.mapHomologicalComplex (.up ℕ)).map (total.map φ (.up ℕ)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply total.hom_ext
  intro q p h
  change q + p = n at h
  change (TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      ((total.map (mapBicomplexMap F φ) (.up ℕ)).f n ≫ TotalComplexFunctor.totalComparisonComponent F L n) =
    (TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫
      (TotalComplexFunctor.totalComparisonComponent F K n ≫ F.map ((total.map φ (.up ℕ)).f n))
  erw [← Category.assoc, ιTotal_map, Category.assoc, TotalComplexFunctor.ι_totalComparisonComponent,
    ← Category.assoc, TotalComplexFunctor.ι_totalComparisonComponent]
  change F.map ((φ.f q).f p) ≫ F.map (L.ιTotal (.up ℕ) q p n h) =
    F.map (K.ιTotal (.up ℕ) q p n h) ≫ F.map ((total.map φ (.up ℕ)).f n)
  exact (F.map_comp _ _).symm.trans
    ((congrArg F.map (ιTotal_map (K := K) (L := L) (φ := φ) (c₁₂ := .up ℕ) q p n h).symm).trans
      (F.map_comp _ _))

end

end OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor
