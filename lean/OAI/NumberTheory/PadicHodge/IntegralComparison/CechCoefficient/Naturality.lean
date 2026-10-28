import OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Total
import OAI.AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor

/-! # Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Naturality.Total

noncomputable section

/-! The coefficient-change isomorphism of native Čech totals commutes
with every map of coefficient complexes. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex₂

universe w uC vC uA vA uB vB

variable {C : Type uC} [Category.{vC} C]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{w} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{w} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{w, w} G]
  (E : SimplicialObject (FormalCoproduct.{w} C))
  {M N : CochainComplex (Cᵒᵖ ⥤ A) ℕ} (f : M ⟶ N)

def bicomplexMap : Total.bicomplex E M ⟶ Total.bicomplex E N :=
  ((FormalCoproduct.cochainComplexFunctor E).mapHomologicalComplex (.up ℕ)).map f

def mappedComplexMap : Total.mappedComplex G M ⟶ Total.mappedComplex G N :=
  (((Functor.whiskeringRight Cᵒᵖ A B).obj G).mapHomologicalComplex (.up ℕ)).map f

variable [HasCoproducts.{0} A] [HasCoproducts.{0} B]

omit [HasCoproducts.{0} A] [HasCoproducts.{0} B] in
theorem bicomplexIso_naturality :
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap E f) ≫ (Total.bicomplexIso G E N).hom =
      (Total.bicomplexIso G E M).hom ≫ bicomplexMap E (mappedComplexMap G f) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact AlgebraicGeometry.Crystalline.Cohomology.Cech.CoefficientChangeNaturality.CechCoefficientChangeNaturality.naturality G E (f.f n)

def totalMap : (Total.bicomplex E M).total (.up ℕ) ⟶ (Total.bicomplex E N).total (.up ℕ) :=
  total.map (bicomplexMap E f) (.up ℕ)

omit [HasCoproducts A] in
theorem totalBicomplexIso_naturality :
    total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap E f)) (.up ℕ) ≫
        (total.mapIso (Total.bicomplexIso G E N) (.up ℕ)).hom =
      (total.mapIso (Total.bicomplexIso G E M) (.up ℕ)).hom ≫
        totalMap E (mappedComplexMap G f) := by
  change total.map _ (.up ℕ) ≫ total.map _ (.up ℕ) =
    total.map _ (.up ℕ) ≫ total.map _ (.up ℕ)
  rw [← total.map_comp, bicomplexIso_naturality, total.map_comp]

variable [HasFiniteBiproducts A]

omit [HasProducts B] [PreservesLimitsOfSize.{w, w, vA, vB, uA, uB} G] in
theorem finiteTotalInverse_naturality :
    (G.mapHomologicalComplex (.up ℕ)).map (totalMap E f) ≫
        (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (Total.bicomplex E N)).inv =
      (AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (Total.bicomplex E M)).inv ≫
        total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap E f)) (.up ℕ) := by
  let e := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (Total.bicomplex E M)
  let d := AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (Total.bicomplex E N)
  have hn : total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap E f)) (.up ℕ) ≫ d.hom =
      e.hom ≫ (G.mapHomologicalComplex (.up ℕ)).map (totalMap E f) :=
    AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.totalComparison_naturality G (bicomplexMap E f)
  calc
    _ = e.inv ≫ (e.hom ≫ (G.mapHomologicalComplex (.up ℕ)).map (totalMap E f)) ≫ d.inv := by
      simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      rfl
    _ = e.inv ≫ (total.map (AlgebraicGeometry.Comparison.Betti.TotalAdditiveFunctor.mapBicomplexMap G (bicomplexMap E f)) (.up ℕ) ≫ d.hom) ≫ d.inv := by
      rw [hn]
    _ = _ := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      rfl

theorem totalIso_naturality :
    (G.mapHomologicalComplex (.up ℕ)).map (totalMap E f) ≫ (Total.totalIso G E N).hom =
      (Total.totalIso G E M).hom ≫ totalMap E (mappedComplexMap G f) := by
  change (G.mapHomologicalComplex (.up ℕ)).map (totalMap E f) ≫
    ((AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (Total.bicomplex E N)).inv ≫
      (total.mapIso (Total.bicomplexIso G E N) (.up ℕ)).hom) =
    ((AlgebraicGeometry.Crystalline.Cohomology.Finite.TotalComparison.FiniteTotalComparison.iso G (Total.bicomplex E M)).inv ≫
      (total.mapIso (Total.bicomplexIso G E M) (.up ℕ)).hom) ≫ _
  rw [← Category.assoc, finiteTotalInverse_naturality, Category.assoc,
    totalBicomplexIso_naturality, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.CechCoefficient.Naturality.Total
