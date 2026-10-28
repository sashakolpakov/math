import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientNaturality

/-! # Coefficient Homology Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientHomologyNaturality.Total

noncomputable section

/-! Coefficient comparison on the original augmented Cech cohomology
is natural for every map of coefficient complexes. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasFiniteBiproducts A]
  [G.PreservesHomology]
  {K L : CochainComplex (Cᵒᵖ ⥤ A) ℕ} (a : K ⟶ L)

theorem homologyIso_naturality (q : ℕ) :
    G.map (homologyMap (CoefficientNaturality.Total.totalMap U a) q) ≫ (CoefficientTotal.homologyIso U G L q).hom =
      (CoefficientTotal.homologyIso U G K q).hom ≫ homologyMap (CoefficientNaturality.Total.totalMap U (CoefficientNaturality.Total.mappedComplexMap G a)) q := by
  have ht := congrArg (fun f => homologyMap f q) (CoefficientNaturality.Total.totalIso_naturality U G a)
  simp only [homologyMap_comp] at ht
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor A (.up ℕ) q).map (CoefficientNaturality.Total.totalMap U a)) G
  change G.map (homologyMap (CoefficientNaturality.Total.totalMap U a) q) ≫
      ((((AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ)).sc q).mapHomologyIso G).inv =
    ((((AugmentedOrdered.CechFunctor.bicomplex U K).total (.up ℕ)).sc q).mapHomologyIso G).inv ≫
      homologyMap ((G.mapHomologicalComplex (.up ℕ)).map (CoefficientNaturality.Total.totalMap U a)) q at hn
  change G.map (homologyMap (CoefficientNaturality.Total.totalMap U a) q) ≫
      (((((AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ)).sc q).mapHomologyIso G).inv ≫
        homologyMap (CoefficientTotal.totalIso U G L).hom q) =
    (((((AugmentedOrdered.CechFunctor.bicomplex U K).total (.up ℕ)).sc q).mapHomologyIso G).inv ≫
        homologyMap (CoefficientTotal.totalIso U G K).hom q) ≫ _
  rw [← Category.assoc, hn, Category.assoc, ht, ← Category.assoc]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientHomologyNaturality.Total
