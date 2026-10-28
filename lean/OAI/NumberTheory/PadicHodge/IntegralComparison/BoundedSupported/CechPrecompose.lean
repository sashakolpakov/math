import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Cech
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechForgetNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedOrdered.CechHomotopy

/-! # Cech Precompose -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechPrecompose

noncomputable section

/-! Precomposing the actual coefficient comparison precomposes its
map to the original bounded crystalline cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Y.Opens) {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Y.Opens)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I

local instance coefficient_limits : HasLimitsOfSize.{u,u} (ModuleCat.{u+2} R) :=
  ModuleCat.hasLimitsOfSize.{u,u,u+2,u+1}
local instance coefficient_colimits : HasColimitsOfSize.{0,0} (ModuleCat.{u+2} R) :=
  ModuleCat.hasColimitsOfSize.{u+2,u+1,0,0} R

variable (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hrows : ∀ q m, ((Cech.bicomplex fY n I F U).X q).ExactAt (m+1))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)
  {L M : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ}
  (c : L ⟶ M)
  (a : M ⟶ Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F
    (BoundedOpen.FlasqueComplex.complex fY n I))

theorem comparison (i : ℕ) :
    Cech.map fY n I F U O hO hcover hrows hglobal L (c ≫ a) i =
      HomologicalComplex.homologyMap (AugmentedOrdered.CechForgetNaturality.map U c) i ≫
        Cech.map fY n I F U O hO hcover hrows hglobal M a i := by
  change HomologicalComplex.homologyMap
      (HomologicalComplex₂.total.map
        (((AugmentedOrdered.CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map (c ≫ a)) (.up ℕ)) i ≫ _ = _
  rw [AugmentedOrdered.CechHomotopy.homology_comp, Category.assoc]
  rfl

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechPrecompose
