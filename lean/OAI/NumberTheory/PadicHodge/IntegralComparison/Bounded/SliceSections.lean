import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceCohomology

/-! # Slice Sections -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceSections

noncomputable section

/-!
# IntegralComparison: constant-source sections for actual bounded slice direct image
-/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceImage

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (U : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.constantUnit (p := p) (J := J) (δ := δ) f n
local notation "AU" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.SliceSheaves.constantUnit f n U

def constantUnitIso : (SliceImage.restriction f n U).obj A ≅ AU :=
  ((Over.forget U).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) ((BoundedCrystalline.Site.topology f n).over U) (BoundedCrystalline.Site.topology f n)).symm.app
      ((Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)ᵒᵖ).obj
        (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))))

def sourceHomEquiv (M : BoundedCrystalline.SliceSheaves.SliceSheaf f n U) :
    ((SliceImage.restriction f n U).obj A ⟶ M) ≃+ (AU ⟶ M) where
  toEquiv := Iso.homCongr (constantUnitIso f n U) (Iso.refl M)
  map_add' a b := by
    change (constantUnitIso f n U).inv ≫ (a + b) ≫ 𝟙 M =
      ((constantUnitIso f n U).inv ≫ a ≫ 𝟙 M) + ((constantUnitIso f n U).inv ≫ b ≫ 𝟙 M)
    rw [Preadditive.add_comp, Preadditive.comp_add]

def homEquiv (M : BoundedCrystalline.SliceSheaves.SliceSheaf f n U) :
    (A ⟶ (SliceImage.directImage f n U).obj M) ≃+ (AU ⟶ M) :=
  ((SliceImage.adjunction f n U).homAddEquiv A M).symm.trans (sourceHomEquiv f n U M)

theorem homEquiv_apply (M : BoundedCrystalline.SliceSheaves.SliceSheaf f n U)
    (a : A ⟶ (SliceImage.directImage f n U).obj M) :
    SliceSections.homEquiv f n U M a = (constantUnitIso f n U).inv ≫ ((SliceImage.adjunction f n U).homEquiv A M).symm a :=
  congrArg (fun t => (constantUnitIso f n U).inv ≫ t)
    (Category.comp_id (((SliceImage.adjunction f n U).homEquiv A M).symm a))

theorem homEquiv_natural {M N : BoundedCrystalline.SliceSheaves.SliceSheaf f n U}
    (a : A ⟶ (SliceImage.directImage f n U).obj M) (b : M ⟶ N) :
    SliceSections.homEquiv f n U N (a ≫ (SliceImage.directImage f n U).map b) = SliceSections.homEquiv f n U M a ≫ b := by
  rw [homEquiv_apply, (SliceImage.adjunction f n U).homEquiv_naturality_right_symm, homEquiv_apply, Category.assoc]

def degreeZeroEquiv (M : BoundedCrystalline.SliceSheaves.SliceSheaf f n U) :
    Abelian.Ext.{u + 2} A ((SliceImage.directImage f n U).obj M) 0 ≃+ Abelian.Ext.{u + 2} AU M 0 :=
  Abelian.Ext.addEquiv₀.trans ((SliceSections.homEquiv f n U M).trans Abelian.Ext.addEquiv₀.symm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SliceSections
