import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientHomologyNaturality

/-! # Coefficient Factor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientFactor

noncomputable section

/-! A genuine map out of a coefficient-changed supported complex
retains its original cohomology map through the canonical source iso. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u uA vA uB vB
open OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientHomologyNaturality.Total
variable {C : Type u} [Preorder C] [HasFiniteProducts C]
  {ι : Type u} [LinearOrder ι] (U : ι → C)
  {A : Type uA} [Category.{vA} A] [Abelian A] [HasProducts.{u} A] [HasCoproducts.{0} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasProducts.{u} B] [HasCoproducts.{0} B]
  (G : A ⥤ B) [G.Additive] [G.PreservesHomology] [PreservesLimitsOfSize.{u,u} G]
  [HasFiniteBiproducts A]
  {K L : CochainComplex (Cᵒᵖ ⥤ A) ℕ} {O : CochainComplex (Cᵒᵖ ⥤ B) ℕ}
  (e : O ≅ CoefficientTotal.mapped G K)

def totalFunctor : CochainComplex (Cᵒᵖ ⥤ B) ℕ ⥤ CochainComplex B ℕ :=
  (AugmentedOrdered.CechFunctor.functor U).mapHomologicalComplex (.up ℕ) ⋙
    HomologicalComplex₂.totalFunctor B (.up ℕ) (.up ℕ) (.up ℕ)

def inputIso (q : ℕ) :=
  CoefficientTotal.homologyIso U G K q ≪≫ (homologyMapIso ((CoefficientFactor.totalFunctor U).mapIso e) q).symm

variable (a : K ⟶ L) (t : O ⟶ CoefficientTotal.mapped G L)
  (ht : t = e.hom ≫ CoefficientNaturality.Total.mappedComplexMap G a) (q : ℕ)
  {T : A} (b : ((AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ)).homology q ⟶ T)

def map := homologyMap (CoefficientNaturality.Total.totalMap U t) q ≫ (CoefficientTotal.homologyIso U G L q).inv ≫ G.map b

include ht in
theorem comparison : (inputIso U G e q).hom ≫ CoefficientFactor.map U G t q b =
    G.map (homologyMap (CoefficientNaturality.Total.totalMap U a) q ≫ b) := by
  subst t
  have hm : CoefficientNaturality.Total.totalMap U (e.hom ≫ CoefficientNaturality.Total.mappedComplexMap G a) =
      CoefficientNaturality.Total.totalMap U e.hom ≫ CoefficientNaturality.Total.totalMap U (CoefficientNaturality.Total.mappedComplexMap G a) := by
    simp only [CoefficientNaturality.Total.totalMap, CoefficientNaturality.Total.bicomplexMap, Functor.map_comp, HomologicalComplex₂.total.map_comp]
  have h := congrArg (fun z => z ≫ (CoefficientTotal.homologyIso U G L q).inv ≫ G.map b)
    (CoefficientHomologyNaturality.Total.homologyIso_naturality U G a q)
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at h
  unfold inputIso CoefficientFactor.map
  rw [hm, homologyMap_comp]
  change ((CoefficientTotal.homologyIso U G K q).hom ≫
      (homologyMapIso ((CoefficientFactor.totalFunctor U).mapIso e) q).inv) ≫
    ((homologyMapIso ((CoefficientFactor.totalFunctor U).mapIso e) q).hom ≫
      homologyMap (CoefficientNaturality.Total.totalMap U (CoefficientNaturality.Total.mappedComplexMap G a)) q) ≫
        (CoefficientTotal.homologyIso U G L q).inv ≫ G.map b = _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact h.symm.trans (G.map_comp _ _).symm

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientFactor
