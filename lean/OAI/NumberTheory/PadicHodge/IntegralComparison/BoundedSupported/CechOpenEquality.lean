import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Cech

/-! # Cech Open Equality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechOpenEquality

noncomputable section

/-! Equal descriptions of the same geometric opens give the same
map from the actual supported Čech total to bounded cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F G : C ⥤ Y.Opens) (h : F = G)
  {ι : Type u} [LinearOrder ι] (U : ι → C)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I

local instance coefficient_limits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}
local instance coefficient_colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasColimitsOfSize.{u + 2, u + 1, 0, 0} R

variable (L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (a : L ⟶ Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F
    (BoundedOpen.FlasqueComplex.complex fY n I))

def transport : L ⟶ Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2} R Y.carrier G K :=
  a ≫ eqToHom (congrArg
    (fun T => Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2} R Y.carrier T K) h)

variable (O : Y.Opens)
  (hOF : ∀ i, F.obj (U i) ≤ O) (hOG : ∀ i, G.obj (U i) ≤ O)
  (hcoverF : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hcoverG : G.obj (⊤_ C) ⊓ O ≤ ⨆ i, G.obj (U i))
  (hrowsF : ∀ q m, ((Cech.bicomplex fY n I F U).X q).ExactAt (m + 1))
  (hrowsG : ∀ q m, ((Cech.bicomplex fY n I G U).X q).ExactAt (m + 1))
  (hglobalF : F.obj (⊤_ C) ⊔ O = ⊤) (hglobalG : G.obj (⊤_ C) ⊔ O = ⊤)

theorem comparison (i : ℕ) :
    Cech.map fY n I F U O hOF hcoverF hrowsF hglobalF L a i =
      Cech.map fY n I G U O hOG hcoverG hrowsG hglobalG L
        (transport fY n I F G h L a) i := by
  subst G
  simp only [transport, eqToHom_refl, Category.comp_id]

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechOpenEquality
