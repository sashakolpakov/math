import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

/-! # Total -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.Total

noncomputable section

/-! Actual total comparison for additive functors uses only finite coproducts on nonnegative diagonals. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

open OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

local instance finiteTotalExists {E : Type*} [Category* E] [Preadditive E]
    [HasFiniteCoproducts E] (B : HomologicalComplex₂ E (.up ℕ) (.up ℕ)) : B.HasTotal (.up ℕ) :=
  TotalExists.hasTotal_of_finiteCoproducts B

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasFiniteCoproducts C] [HasFiniteCoproducts D] (F : C ⥤ D) [F.Additive]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

def totalComparisonComponent (n : ℕ) :
    ((TotalComplexFunctor.mapBicomplex F K).total (.up ℕ)).X n ⟶ F.obj ((K.total (.up ℕ)).X n) := by
  have : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) := by
    change Finite {p : ℕ × ℕ // p.1 + p.2 = n}
    exact TotalDiagonal.finiteTotalDiagonal n
  exact sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)

theorem ι_totalComparisonComponent (q p n : ℕ) (h : q + p = n) :
    (TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫ totalComparisonComponent F K n =
      F.map (K.ιTotal (.up ℕ) q p n h) := by
  have : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) := by
    change Finite {p : ℕ × ℕ // p.1 + p.2 = n}
    exact TotalDiagonal.finiteTotalDiagonal n
  exact ι_comp_sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) ⟨(q, p), h⟩

theorem totalComparisonComponent_comm (n : ℕ) :
    totalComparisonComponent F K n ≫ F.map ((K.total (.up ℕ)).d n (n + 1)) =
      ((TotalComplexFunctor.mapBicomplex F K).total (.up ℕ)).d n (n + 1) ≫ totalComparisonComponent F K (n + 1) := by
  let M := TotalComplexFunctor.mapBicomplex F K
  apply total.hom_ext
  intro q p h
  change q + p = n at h
  subst n
  erw [← Category.assoc, ι_totalComparisonComponent, ← F.map_comp, (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat K)]
  erw [← Category.assoc (M.ιTotal (.up ℕ) q p (q + p) rfl), (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat M)]
  simp only [Functor.map_add, Functor.map_units_smul, F.map_comp, Preadditive.add_comp,
    Linear.units_smul_comp, Category.assoc]
  dsimp only [M]
  erw [ι_totalComparisonComponent, ι_totalComparisonComponent]
  rfl

def totalComparison : (TotalComplexFunctor.mapBicomplex F K).total (.up ℕ) ⟶
    (F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) where
  f := totalComparisonComponent F K
  comm' n m h := by
    change n + 1 = m at h
    subst m
    exact totalComparisonComponent_comm F K n

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.Total
