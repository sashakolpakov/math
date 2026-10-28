import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Cech
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.CoefficientFactor

/-! # Coefficient Factor -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CoefficientFactor

noncomputable section

/-! Changing coefficients in the original supported comparison preserves
its map to the original bounded crystalline cohomology. -/
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry _root_.HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u vD wD
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Y.Opens) {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Y.Opens)

local instance coefficient_limits : HasLimitsOfSize.{u,u} (ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  ModuleCat.hasLimitsOfSize.{u,u,u+2,u+1}
local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) :=
  ModuleCat.hasColimitsOfSize.{u+2,u+1,0,0} (Crystalline.ExactRestriction.Coeff (B := B))

variable (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hrows : ∀ q r, ((Cech.bicomplex fY n I F U).X q).ExactAt (r+1))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)
  {D : Type vD} [Category.{wD} D] [Abelian D] [HasProducts.{u} D] [HasCoproducts.{0} D]
  (G : ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B)) ⥤ D) [G.Additive] [G.PreservesHomology]
  [PreservesLimitsOfSize.{u,u} G]
  {K : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ}
  {P : CochainComplex (Cᵒᵖ ⥤ D) ℕ}
  (e : P ≅ AugmentedCech.CoefficientTotal.mapped G K)
  (a : K ⟶ Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F (BoundedOpen.FlasqueComplex.complex fY n I))
  (t : P ⟶ AugmentedCech.CoefficientTotal.mapped G
    (Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
      (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F (BoundedOpen.FlasqueComplex.complex fY n I)))
  (ht : t = e.hom ≫ AugmentedCech.CoefficientNaturality.Total.mappedComplexMap G a)

include ht in
theorem comparison (q : ℕ) :
    (AugmentedCech.CoefficientFactor.inputIso U G e q).hom ≫
      AugmentedCech.CoefficientFactor.map U G t q
        (Cech.toBounded fY n I F U O hO hcover hrows hglobal q) =
    G.map (Cech.map fY n I F U O hO hcover hrows hglobal K a q) := by
  dsimp only [Cech.map, Cech.cochainMap]
  exact AugmentedCech.CoefficientFactor.comparison U G e a t ht q
    (Cech.toBounded fY n I F U O hO hcover hrows hglobal q)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CoefficientFactor
