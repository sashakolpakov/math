import OAI.NumberTheory.PadicHodge.IntegralComparison.Single.ComplexTransport
import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.RelativeSheafComplex

/-! # Sheaf Augmentation Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafAugmentationZero

noncomputable section

/-!
# IntegralComparison: the original bounded frame sheaf augmentation in degree zero
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f] (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

theorem zero : (RelativeSheafComplex.augmentation f n F).f 0 =
    (RelativeSheafComplex.structureIso f n).inv ≫
      (RelativeSheafComplex.sheafification f n).map
        (RelativeCrystalline.ModuleComplex.augmentationZero (BoundedFrame.Diagram.productDiagram F)
          (BoundedCrystalline.Site.inclusion f n) (BoundedFrame.Diagram.projection F)) := by
  have h := Single.ComplexTransport.map_zero (RelativeSheafComplex.sheafification f n)
    (RelativeSheafComplex.structureIso f n) (BoundedFrame.Diagram.augmentation F)
  exact h.trans (congrArg (fun a => (RelativeSheafComplex.structureIso f n).inv ≫
    (RelativeSheafComplex.sheafification f n).map a)
      (RelativeCrystalline.ModuleComplex.augmentation_zero (BoundedFrame.Diagram.productDiagram F)
        (BoundedCrystalline.Site.inclusion f n) (BoundedFrame.Diagram.projection F)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.SheafAugmentationZero
