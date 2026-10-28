import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps

/-! # Cohomology Transition -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition

noncomputable section

/-!
# IntegralComparison: canonical maps between the original bounded crystalline Ext groups
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site
open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "T" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

def constantUnitIso : (T).obj (BoundedCrystalline.CrystallineCohomology.constantUnit f m) ≅
    BoundedCrystalline.CrystallineCohomology.constantUnit f n :=
  ((I).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B))) (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)).symm.app
      ((Functor.const (BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f m)ᵒᵖ).obj
        (ModuleCat.of (Crystalline.ExactRestriction.Coeff (B := B)) (Crystalline.ExactRestriction.Coeff (B := B))))

def structureIso : (T).obj (BoundedCrystalline.CrystallineCohomology.structureSheaf f m) ≅
    BoundedCrystalline.CrystallineCohomology.structureSheaf f n := Iso.refl _

def map (i : ℕ) : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f m i →ₗ[Crystalline.ExactRestriction.Coeff (B := B)]
    BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := J) (δ := δ) f n i :=
  (Etale.Frobenius.extIsoCongr (Crystalline.ExactRestriction.Coeff (B := B)) (constantUnitIso f n m hnm)
    (structureIso f n m hnm) i).toLinearMap.comp
      ((T).mapExtLinearMap (Crystalline.ExactRestriction.Coeff (B := B))
        (BoundedCrystalline.CrystallineCohomology.constantUnit f m)
        (BoundedCrystalline.CrystallineCohomology.structureSheaf f m) i)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition
