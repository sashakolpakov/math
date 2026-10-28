import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Cech
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentedCech.HomologyFunctor

/-! # Cech Homology -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechHomology

noncomputable section

/-! Equal supported cohomology maps give exactly the same
class in the original bounded crystalline cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C : Type u} [Preorder C] [HasFiniteProducts C]
  (F : C ⥤ Y.Opens) {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Y.Opens)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)

local instance coefficient_limits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}
local instance coefficient_colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasColimitsOfSize.{u + 2, u + 1, 0, 0} R

variable (hO : ∀ i, F.obj (U i) ≤ O)
  (hcover : F.obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (U i))
  (hrows : ∀ q r,
    ((Supported.OrderedCechEdge.bicomplex.{u+1,u,u,u+2}
      (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F U
      (BoundedOpen.FlasqueComplex.complex fY n I)).X q).ExactAt (r + 1))
  (hglobal : F.obj (⊤_ C) ⊔ O = ⊤)
  (L : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u+2} (Crystalline.ExactRestriction.Coeff (B := B))) ℕ)
  (a b : L ⟶ Supported.OrderedCechEdge.presheafComplex.{u+1,u,u,u+2}
    (Crystalline.ExactRestriction.Coeff (B := B)) Y.carrier F
    (BoundedOpen.FlasqueComplex.complex fY n I))

theorem map_eq (i : ℕ)
    (h : (AugmentedCech.HomologyFunctor.functor U i).map a =
      (AugmentedCech.HomologyFunctor.functor U i).map b) :
    Cech.map fY n I F U O hO hcover hrows hglobal L a i =
      Cech.map fY n I F U O hO hcover hrows hglobal L b i :=
  congrArg (fun c => c ≫ Cech.toBounded fY n I F U O hO hcover hrows hglobal i) h

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechHomology
