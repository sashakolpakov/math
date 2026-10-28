import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafAugmentationNormalization
import OAI.NumberTheory.PadicHodge.IntegralComparison.Presheaf.AugmentationPrecompose
import OAI.NumberTheory.PadicHodge.IntegralComparison.FrameCech.IntrinsicTotalCoordinates
import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.CechComplex

/-! # Intrinsic Augmentation Edge -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IntrinsicAugmentationEdge.Intrinsic

noncomputable section

/-! The original bounded crystalline sheaf augmentation induces exactly
its product-preserving ambient-ring Čech total map. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (T : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  {ι : Type u} (F : ι → BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := B)
local notation "Y" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.CrystallineCohomology.structureSheaf
  (p := p) (J := J) (δ := δ) f n
local notation "K" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.complex f n T
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.SheafLeibniz.Product.underlyingComplex f n T
local notation "a" => OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex.augmentation f n T
local notation "N" => OAI.NumberTheory.PadicHodge.IntegralComparison.NonemptyCechNerve.nerve F

local instance coefficientProducts : HasProducts.{u} (ModuleCat.{u + 1} CR) :=
  fun Q => (ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}).has_limits_of_shape (Discrete Q)

theorem closed : ((a).f 0).hom ≫ (P).d 0 1 = 0 :=
  congrArg (fun b : Y ⟶ (K).X 1 => b.hom)
    (Augmented.ResolutionCycles.augmentation_condition K a)

def edge := FrameCech.IntrinsicTotalCoordinates.Intrinsic.edge.{u + 1, u} F CR (BoundedCrystalline.Site.topology f n) K a

theorem edge_eq : edge f n T F =
    Presheaf.AugmentationProduct.map.{u + 1, u, u, u + 1, u + 1}
      N P (Y).obj ((a).f 0).hom (closed f n T) :=
  (Presheaf.AugmentationEdge.map_eq_edge.{u + 1, u, u, u + 1, u + 1}
    N P (Y).obj ((a).f 0).hom (closed f n T)).symm

theorem square : (BoundedFrame.CechComplex.presheafIso f n F).hom ≫ edge f n T F =
    BoundedFrame.SheafAugmentationProduct.totalMap f n T N := by
  rw [edge_eq]
  exact Presheaf.AugmentationPrecompose.map.{u + 1, u, u, u + 1, u + 1}
    N P (SheafAugmentationNormalization.structureMap f n)
    (BoundedFrame.SheafAugmentationProduct.augmentation f n T)
    (BoundedFrame.SheafAugmentationProduct.augmentation_closed f n T)
    ((a).f 0).hom (closed f n T) (SheafAugmentationNormalization.zero f n T)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.IntrinsicAugmentationEdge.Intrinsic
