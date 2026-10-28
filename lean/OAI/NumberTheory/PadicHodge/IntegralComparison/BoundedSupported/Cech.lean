import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCech
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Sections

/-! # Cech -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Cech

noncomputable section

/-! The supported ordered Čech construction lands in the original
bounded crystalline cohomology through its actual injective resolution. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

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
local notation "V" => F.obj (⊤_ C)

local instance coefficient_limits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}

local instance coefficient_colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasColimitsOfSize.{u + 2, u + 1, 0, 0} R

def bicomplex := Supported.OrderedCechEdge.bicomplex.{u+1,u,u,u+2} R Y.carrier F U K

variable (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hrows : ∀ q r,
    ((Supported.OrderedCechEdge.bicomplex.{u+1,u,u,u+2}
      (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F U
      (BoundedOpen.FlasqueComplex.complex fY n I)).X q).ExactAt (r + 1))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)

def toBounded (i : ℕ) : ((bicomplex fY n I F U).total (.up ℕ)).homology i ⟶
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology
      (p := p) (J := J) (δ := δ) fY n i) :=
  (Supported.OrderedCech.Comparison.homologyIso.{u+1,u,u,u+2}
    R Y.carrier F U O K hO hcover hrows i).inv ≫
      Sections.forgetSupport fY n I O V hglobal i

theorem edge_toBounded (i : ℕ) :
    HomologicalComplex.homologyMap
      (Supported.OrderedCechEdge.map.{u+1,u,u,u+2} R Y.carrier F U O K hO) i ≫
        toBounded fY n I F U O hO hcover hrows hglobal i =
    Sections.forgetSupport fY n I O V hglobal i := by
  change (Supported.OrderedCech.Comparison.homologyIso.{u+1,u,u,u+2}
    R Y.carrier F U O K hO hcover hrows i).hom ≫
      ((Supported.OrderedCech.Comparison.homologyIso.{u+1,u,u,u+2}
        R Y.carrier F U O K hO hcover hrows i).inv ≫ _) = _
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

variable (L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (a : L ⟶ Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F
    (BoundedOpen.FlasqueComplex.complex fY n I))

def cochainMap : (AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ) ⟶
    (bicomplex fY n I F U).total (.up ℕ) :=
  HomologicalComplex₂.total.map
    (((AugmentedOrdered.CechFunctor.functor U).mapHomologicalComplex (.up ℕ)).map a) (.up ℕ)

def map (i : ℕ) : ((AugmentedOrdered.CechFunctor.bicomplex U L).total (.up ℕ)).homology i ⟶
    ModuleCat.of R (BoundedCrystalline.CrystallineCohomology.Cohomology
      (p := p) (J := J) (δ := δ) fY n i) :=
  HomologicalComplex.homologyMap (cochainMap fY n I F U L a) i ≫
    toBounded fY n I F U O hO hcover hrows hglobal i

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Cech
