import OAI.NumberTheory.PadicHodge.IntegralComparison.AdjunctionAugmentationNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafAugmentationZero
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentationProduct
import OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.StructureDescent

/-! # Sheaf Augmentation Normalization -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafAugmentationNormalization

noncomputable section

/-! The actual bounded crystalline structure augmentation is exactly the
ring coefficient augmentation used by the native PD Čech product. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "O" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := J) (δ := δ) f n
local notation "A" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafAugmentationProduct.ambient
  (p := p) (J := J) (δ := δ) f n

def structureMap : A ⟶ (O).obj :=
  Functor.whiskerLeft (BoundedCrystalline.Site.inclusion f n).op (Crystalline.StructureDescent.structurePresheafIso f).hom

omit [Fact (Nat.Prime p)] [IsSeparated f] in
theorem structureMap_unit :
    toSheafify (BoundedCrystalline.Site.topology f n) A ≫ (RelativeSheafComplex.structureIso f n).hom.hom =
      structureMap f n :=
  (BoundedCrystalline.Site.inclusion f n).toSheafify_pullbackSheafificationCompatibility
    (ModuleCat.{u + 1} CR) (BoundedCrystalline.Site.topology f n) BigCrystallineSite.Object.topology
    (BigCrystallineCohomology.largePresheaf f)

theorem zero : structureMap f n ≫ ((RelativeSheafComplex.augmentation f n F).f 0).hom =
    BoundedFrame.SheafAugmentationProduct.augmentation f n F := by
  exact AdjunctionAugmentationNormalization.normalization
    (sheafificationAdjunction (BoundedCrystalline.Site.topology f n) (ModuleCat.{u + 1} CR))
    (RelativeSheafComplex.structureIso f n)
    (structureMap f n) (structureMap_unit f n)
    (BoundedFrame.SheafAugmentationProduct.coefficientAugmentation f n F)
    ((RelativeSheafComplex.augmentation f n F).f 0)
    (SheafAugmentationZero.zero f n F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafAugmentationNormalization
