import OAI.AlgebraicGeometry.Comparison.Betti.TotalExists

/-! # Total Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor

noncomputable section

/-! Totalization commutes with additive functors using only finite coproducts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

local instance (n : ℕ) : Finite ((ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) ⁻¹' {n}) := by
  change Finite {p : ℕ × ℕ // p.1 + p.2 = n}
  exact TotalDiagonal.finiteTotalDiagonal n

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasFiniteCoproducts C] [HasFiniteCoproducts D] (F : C ⥤ D) [F.Additive]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

local instance : K.HasTotal (.up ℕ) := TotalExists.hasTotal_of_finiteCoproducts K
local instance : (TotalComplexFunctor.mapBicomplex F K).HasTotal (.up ℕ) :=
  TotalExists.hasTotal_of_finiteCoproducts (TotalComplexFunctor.mapBicomplex F K)

def finiteTotalComparisonComponent (n : ℕ) :
    ((TotalComplexFunctor.mapBicomplex F K).total (.up ℕ)).X n ⟶ F.obj ((K.total (.up ℕ)).X n) :=
  sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)

theorem ι_finiteTotalComparisonComponent (q p n : ℕ) (h : q + p = n) :
    (TotalComplexFunctor.mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫ finiteTotalComparisonComponent F K n =
      F.map (K.ιTotal (.up ℕ) q p n h) :=
  ι_comp_sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) ⟨(q, p), h⟩

theorem finiteTotalComparisonComponent_comm (n : ℕ) :
    finiteTotalComparisonComponent F K n ≫ F.map ((K.total (.up ℕ)).d n (n + 1)) =
      ((TotalComplexFunctor.mapBicomplex F K).total (.up ℕ)).d n (n + 1) ≫ finiteTotalComparisonComponent F K (n + 1) := by
  let M := TotalComplexFunctor.mapBicomplex F K
  apply total.hom_ext
  intro q p h
  change q + p = n at h
  subst n
  erw [← Category.assoc, ι_finiteTotalComparisonComponent, ← F.map_comp, (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat K)]
  erw [← Category.assoc (M.ιTotal (.up ℕ) q p (q + p) rfl), (SheafCohomology.Cech.UpNatLowDegrees.HomologicalComplex₂.ιTotal_d_upNat M)]
  simp only [Functor.map_add, Functor.map_units_smul, F.map_comp, Preadditive.add_comp,
    Linear.units_smul_comp, Category.assoc]
  dsimp only [M]
  erw [ι_finiteTotalComparisonComponent, ι_finiteTotalComparisonComponent]
  rfl

def finiteTotalComparison : (TotalComplexFunctor.mapBicomplex F K).total (.up ℕ) ⟶
    (F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) where
  f := finiteTotalComparisonComponent F K
  comm' n m h := by
    change n + 1 = m at h
    subst m
    exact finiteTotalComparisonComponent_comm F K n

instance finiteTotalComparisonComponent_isIso (n : ℕ) :
    IsIso (finiteTotalComparisonComponent F K n) :=
  inferInstanceAs (IsIso (sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)))

def finiteTotalComparisonIso : (TotalComplexFunctor.mapBicomplex F K).total (.up ℕ) ≅
    (F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) := by
  have (n : ℕ) : IsIso ((finiteTotalComparison F K).f n) := finiteTotalComparisonComponent_isIso F K n
  have : IsIso (finiteTotalComparison F K) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (finiteTotalComparison F K)

end

end OAI.AlgebraicGeometry.Comparison.Betti.Finite.TotalFunctor
