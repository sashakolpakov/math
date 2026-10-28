import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientForget

/-! # Coefficient Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientHomology

noncomputable section

/-! The exact coefficient-change isomorphism commutes with the
original support-forgetting map on cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex Opposite
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vA uA vB uB
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasProducts.{u} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasProducts.{u} B]
  (G : A ⥤ B) [G.Additive] [PreservesLimitsOfSize.{u,u} G]
  [HasCoproducts.{0} A] [HasCoproducts.{0} B] [HasFiniteBiproducts A]
  [CategoryWithHomology A] [CategoryWithHomology B] [G.PreservesHomology]
  (K : CochainComplex (Cᵒᵖ ⥤ A) ℕ)

def ambientIso (q : ℕ) : G.obj ((AugmentedOrdered.CechForget.ambientComplex K).homology q) ≅
    (AugmentedOrdered.CechForget.ambientComplex (CoefficientTotal.mapped G K)).homology q :=
  (((AugmentedOrdered.CechForget.ambientComplex K).sc q).mapHomologyIso G).symm

theorem comparison (q : ℕ) : (CoefficientTotal.homologyIso U G K q).hom ≫
    homologyMap (AugmentedOrdered.CechForget.forgetSupport U (CoefficientTotal.mapped G K)) q =
      G.map (homologyMap (AugmentedOrdered.CechForget.forgetSupport U K) q) ≫ (ambientIso G K q).hom := by
  have h := congrArg (fun a => homologyMap a q)
    (CoefficientForget.comparison U G K)
  simp only [homologyMap_comp] at h
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((shortComplexFunctor A (.up ℕ) q).map (AugmentedOrdered.CechForget.forgetSupport U K)) G
  change (((((AugmentedOrdered.CechFunctor.bicomplex U K).total (.up ℕ)).sc q).mapHomologyIso G).inv ≫
    homologyMap (CoefficientTotal.totalIso U G K).hom q) ≫ homologyMap (AugmentedOrdered.CechForget.forgetSupport U (CoefficientTotal.mapped G K)) q = _
  rw [Category.assoc, h]
  exact hn.symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientHomology
