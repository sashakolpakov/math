import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.StructureSquare

/-! # Sheafification Structure -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.SheafificationStructure

noncomputable section

/-!
# IntegralComparison: the frame sheafification comparison preserves the original structure isomorphism
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeCrystalline.ModuleComplex.ambientPresheaf QY
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.restriction (p := p) (J := J) (δ := δ) f n m hnm

theorem comparison_inv : (FrameSheaves.sheafificationIso f n m hnm).inv.app A =
    ((G).pushforwardContinuousSheafificationCompatibility (ModuleCat.{u + 1} (Crystalline.ExactRestriction.Coeff (B := B)))
      (BoundedCrystalline.Site.topology f n) (BoundedCrystalline.Site.topology f m)).hom.app
        ((QY).op ⋙ BigCrystallineCohomology.largePresheaf f) := rfl

theorem square : (FrameSheaves.sheafificationIso f n m hnm).inv.app A ≫
    (R).map (Bounded.RelativeSheafComplex.structureIso f m).hom ≫
      (Bounded.CohomologyTransition.structureIso f n m hnm).hom =
        (Bounded.RelativeSheafComplex.structureIso (p := p) (J := J) (δ := δ) f n).hom := by
  exact (congrArg (fun a => a ≫ (R).map (Bounded.RelativeSheafComplex.structureIso f m).hom ≫
    (Bounded.CohomologyTransition.structureIso f n m hnm).hom) (comparison_inv f n m hnm)).trans
      (StructureSquare.square f n m hnm)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.SheafificationStructure
