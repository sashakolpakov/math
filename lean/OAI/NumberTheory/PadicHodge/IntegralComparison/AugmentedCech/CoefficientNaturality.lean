import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientTotal
import OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor

/-! # Coefficient Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientNaturality.Total

noncomputable section

/-! The coefficient-change isomorphism of native Čech totals commutes
with every map of coefficient complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

universe u uA vA uB vB

variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u, u} G]
  {M N : CochainComplex (Cᵒᵖ ⥤ A) ℕ} (f : M ⟶ N)

def bicomplexMap : AugmentedOrdered.CechFunctor.bicomplex U M ⟶ AugmentedOrdered.CechFunctor.bicomplex U N :=
  ((AugmentedOrdered.CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map f

def mappedComplexMap : CoefficientTotal.mapped G M ⟶ CoefficientTotal.mapped G N :=
  (((Functor.whiskeringRight Cᵒᵖ A B).obj G).mapHomologicalComplex (.up ℕ)).map f

variable [HasCoproducts.{0} A] [HasCoproducts.{0} B]

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplexIso_naturality :
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap U f) ≫ (CoefficientTotal.bicomplexIso U G N).hom =
      (CoefficientTotal.bicomplexIso U G M).hom ≫ bicomplexMap U (mappedComplexMap G f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact CoefficientChange.naturality U G (M.X n) (f.f n)

def totalMap : (AugmentedOrdered.CechFunctor.bicomplex U M).total (.up ℕ) ⟶ (AugmentedOrdered.CechFunctor.bicomplex U N).total (.up ℕ) :=
  total.map (bicomplexMap U f) (.up ℕ)

omit [HasCoproducts A] in
theorem totalBicomplexIso_naturality :
    total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap U f)) (.up ℕ) ≫
        (total.mapIso (CoefficientTotal.bicomplexIso U G N) (.up ℕ)).hom =
      (total.mapIso (CoefficientTotal.bicomplexIso U G M) (.up ℕ)).hom ≫
        totalMap U (mappedComplexMap G f) := by
  change total.map _ (.up ℕ) ≫ total.map _ (.up ℕ) =
    total.map _ (.up ℕ) ≫ total.map _ (.up ℕ)
  rw [← total.map_comp, bicomplexIso_naturality, total.map_comp]

variable [HasFiniteBiproducts A]

omit [HasProducts B] [PreservesLimitsOfSize.{u, u, vA, vB, uA, uB} G] in
theorem finiteTotalInverse_naturality :
    (G.mapHomologicalComplex (.up ℕ)).map (totalMap U f) ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AugmentedOrdered.CechFunctor.bicomplex U N)).inv =
      (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AugmentedOrdered.CechFunctor.bicomplex U M)).inv ≫
        total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap U f)) (.up ℕ) := by
  let e := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AugmentedOrdered.CechFunctor.bicomplex U M)
  let d := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AugmentedOrdered.CechFunctor.bicomplex U N)
  have hn : total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap U f)) (.up ℕ) ≫ d.hom =
      e.hom ≫ (G.mapHomologicalComplex (.up ℕ)).map (totalMap U f) :=
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.totalComparison_naturality G (bicomplexMap U f)
  calc
    _ = e.inv ≫ (e.hom ≫ (G.mapHomologicalComplex (.up ℕ)).map (totalMap U f)) ≫ d.inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      rfl
    _ = e.inv ≫ (total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap U f)) (.up ℕ) ≫ d.hom) ≫ d.inv := by
      rw [hn]
    _ = _ := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl

theorem totalIso_naturality :
    (G.mapHomologicalComplex (.up ℕ)).map (totalMap U f) ≫ (CoefficientTotal.totalIso U G N).hom =
      (CoefficientTotal.totalIso U G M).hom ≫ totalMap U (mappedComplexMap G f) := by
  change (G.mapHomologicalComplex (.up ℕ)).map (totalMap U f) ≫
    ((AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AugmentedOrdered.CechFunctor.bicomplex U N)).inv ≫
      (total.mapIso (CoefficientTotal.bicomplexIso U G N) (.up ℕ)).hom) =
    ((AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (AugmentedOrdered.CechFunctor.bicomplex U M)).inv ≫
      (total.mapIso (CoefficientTotal.bicomplexIso U G M) (.up ℕ)).hom) ≫ _
  rw [← Category.assoc, finiteTotalInverse_naturality, Category.assoc,
    totalBicomplexIso_naturality, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientNaturality.Total
