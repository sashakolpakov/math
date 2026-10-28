import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.Cech
import OAI.NumberTheory.PadicHodge.IntegralComparison.Supported.OrderedCechReindexHomology

/-! # Cech Reindex -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechReindex

noncomputable section

/-! Reindexing the actual supported Čech cover preserves its map
to the original bounded crystalline cohomology. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {Y : Scheme.{u}} (fY : Y ⟶ Spec (CommRingCat.of B)) (n : ℕ)
  (I : InjectiveResolution (BoundedCrystalline.CrystallineCohomology.structureSheaf
    (p := p) (J := J) (δ := δ) fY n))
  {C D : Type u} [Preorder C] [HasFiniteProducts C] [Preorder D] [HasFiniteProducts D]
  (r : C ⥤ D) [PreservesFiniteProducts r] (F : D ⥤ Y.Opens)
  {ι : Type u} [LinearOrder ι] (U : ι → C) (O : Y.Opens)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.FlasqueComplex.complex fY n I

local instance coefficient_limits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 2, u + 1}
local instance coefficient_colimits : HasColimitsOfSize.{0, 0} (ModuleCat.{u + 2} R) :=
  ModuleCat.hasColimitsOfSize.{u + 2, u + 1, 0, 0} R

def totalIso :
    ((Cech.bicomplex fY n I (r ⋙ F) U).total (.up ℕ)) ≅
      ((Cech.bicomplex fY n I F (r.obj ∘ U)).total (.up ℕ)) :=
  Supported.OrderedCechReindex.totalIso R Y.carrier r F U K

variable (hO : ∀ i, F.obj (r.obj (U i)) ≤ O)
  (hcoverC : (r ⋙ F).obj (⊤_ C) ⊓ O ≤ ⨆ i, F.obj (r.obj (U i)))
  (hcoverD : F.obj (⊤_ D) ⊓ O ≤ ⨆ i, F.obj (r.obj (U i)))
  (hrowsC : ∀ q m, ((Cech.bicomplex fY n I (r ⋙ F) U).X q).ExactAt (m + 1))
  (hrowsD : ∀ q m, ((Cech.bicomplex fY n I F (r.obj ∘ U)).X q).ExactAt (m + 1))
  (hglobalC : (r ⋙ F).obj (⊤_ C) ⊔ O = ⊤)
  (hglobalD : F.obj (⊤_ D) ⊔ O = ⊤)

theorem comparison (i : ℕ) :
    HomologicalComplex.homologyMap (totalIso fY n I r F U).hom i ≫
      Cech.toBounded fY n I F (r.obj ∘ U) O hO hcoverD hrowsD hglobalD i =
    Cech.toBounded fY n I (r ⋙ F) U O hO hcoverC hrowsC hglobalC i := by
  have h := Supported.OrderedCechReindexHomology.comparison R Y.carrier r F U O K
    hO hcoverC hcoverD hrowsC hrowsD hglobalC hglobalD i
  have hs := congrArg (fun a => a ≫ (BoundedOpen.SectionGlobal.homologyIso fY n I i).hom) h
  simpa only [totalIso, Cech.toBounded,
    Sections.forgetSupport, Sections.extension,
    Supported.OrderedCech.Comparison.forgetSupport, Category.assoc] using hs

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedSupported.CechReindex
