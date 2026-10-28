import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameAugmentation

/-! # Frame Augmentation Zero -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameAugmentationZero

noncomputable section

/-!
# IntegralComparison: the geometric frame restriction comparison preserves degree-zero ring sections
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n

omit [IsSeparated f] in
theorem mapped_zero : (FrameAugmentation.mappedAugmentation g hg n F).f 0 =
    (Relative.ComplexRestriction.restriction (B := B) G).map
      (RelativeCrystalline.ModuleComplex.augmentationZero (BoundedFrame.Diagram.productDiagram ((G).obj F))
        QY (BoundedFrame.Diagram.projection ((G).obj F))) := by
  have h := Relative.RestrictionAugmentation.mappedAugmentation_zero G
    (BoundedFrame.Diagram.productDiagram ((G).obj F)) QY (BoundedFrame.Diagram.projection ((G).obj F))
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact congrArg (fun η => η.app U a) h

theorem zero : (Relative.ComplexRestriction.restriction (B := B) G).map
    (RelativeCrystalline.ModuleComplex.augmentationZero (BoundedFrame.Diagram.productDiagram ((G).obj F))
      QY (BoundedFrame.Diagram.projection ((G).obj F))) ≫
        (FrameRestriction.presheafMap g hg n F).f 0 =
    RelativeCrystalline.ModuleComplex.augmentationZero (BoundedFrame.Diagram.productDiagram F) QX
      (BoundedFrame.Diagram.projection F) := by
  have h := congrArg (fun η => η.f 0) (FrameAugmentation.augmentation g hg n F)
  have h₀ := mapped_zero g hg n F
  have h₁ := RelativeCrystalline.ModuleComplex.augmentation_zero (BoundedFrame.Diagram.productDiagram F) QX
    (BoundedFrame.Diagram.projection F)
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have h₀a := congrArg (fun η => (FrameRestriction.presheafMap g hg n F).f 0 |>.app U <| η.app U a) h₀
  have ha := congrArg (fun η => η.app U a) h
  have h₁a := congrArg (fun η => η.app U a) h₁
  exact h₀a.symm.trans (ha.trans h₁a)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameAugmentationZero
