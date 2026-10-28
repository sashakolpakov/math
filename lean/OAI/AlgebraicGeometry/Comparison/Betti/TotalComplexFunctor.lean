import OAI.AlgebraicGeometry.SheafCohomology.Cech.UpNatLowDegrees
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Total Complex Functor -/

namespace OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor

noncomputable section

/-! Additive functors commute with first-quadrant total complexes when they preserve coproducts. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  [HasCoproducts.{0} C] [HasCoproducts.{0} D] (F : C ⥤ D) [F.Additive]
  (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ))

def mapBicomplex : HomologicalComplex₂ D (.up ℕ) (.up ℕ) :=
  ((F.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj K

def totalComparisonComponent (n : ℕ) :
    ((mapBicomplex F K).total (.up ℕ)).X n ⟶ F.obj ((K.total (.up ℕ)).X n) :=
  sigmaComparison F (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)

theorem ι_totalComparisonComponent (q p n : ℕ) (h : q + p = n) :
    (mapBicomplex F K).ιTotal (.up ℕ) q p n h ≫ totalComparisonComponent F K n =
      F.map (K.ιTotal (.up ℕ) q p n h) :=
  ι_comp_sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n) ⟨(q, p), h⟩

theorem totalComparisonComponent_comm (n : ℕ) :
    totalComparisonComponent F K n ≫ F.map ((K.total (.up ℕ)).d n (n + 1)) =
      ((mapBicomplex F K).total (.up ℕ)).d n (n + 1) ≫ totalComparisonComponent F K (n + 1) := by
  let M := mapBicomplex F K
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

def totalComparison : (mapBicomplex F K).total (.up ℕ) ⟶
    (F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) where
  f := totalComparisonComponent F K
  comm' n m h := by
    change n + 1 = m at h
    subst m
    exact totalComparisonComponent_comm F K n

instance totalComparisonComponent_isIso [PreservesColimitsOfSize.{0, 0} F] (n : ℕ) :
    IsIso (totalComparisonComponent F K n) :=
  inferInstanceAs (IsIso (sigmaComparison F
    (K.toGradedObject.mapObjFun (ComplexShape.π (.up ℕ) (.up ℕ) (.up ℕ)) n)))

def totalComparisonIso [PreservesColimitsOfSize.{0, 0} F] :
    (mapBicomplex F K).total (.up ℕ) ≅
      (F.mapHomologicalComplex (.up ℕ)).obj (K.total (.up ℕ)) := by
  have (n : ℕ) : IsIso ((totalComparison F K).f n) := totalComparisonComponent_isIso F K n
  have : IsIso (totalComparison F K) := HomologicalComplex.Hom.isIso_of_components _
  exact asIso (totalComparison F K)

end

end OAI.AlgebraicGeometry.Comparison.Betti.TotalComplexFunctor
