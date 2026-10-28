import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.RestrictionAugmentation

/-! # Frame Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameAugmentation

noncomputable section

/-! Restricting a native frame between bounded crystalline levels preserves its structure augmentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.LevelFrameComparison

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m) (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram (Functor.obj
  (BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm) F)
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection (Functor.obj
  (BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm) F)

def mappedAugmentation : (CochainComplex.single₀ _).obj (RelativeCrystalline.ModuleComplex.ambientPresheaf QX) ⟶
    ((Relative.ComplexRestriction.restriction (B := B) G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (BoundedFrame.Diagram.complex ((G).obj F)) :=
  Relative.RestrictionAugmentation.mappedAugmentation G P QY π

theorem restriction_augmentation : mappedAugmentation f n m hnm F ≫
    (FrameRestriction.restrictionIso f n m hnm F).hom =
      RelativeCrystalline.ModuleComplex.augmentation (LevelFrameComparison.targetDiagram f n m hnm F) (G ⋙ QY)
        (LevelFrameComparison.targetProjection f n m hnm F) :=
  Relative.RestrictionAugmentation.augmentation G P QY π

theorem diagram_augmentation : RelativeCrystalline.ModuleComplex.augmentation
    (LevelFrameComparison.targetDiagram f n m hnm F) (G ⋙ QY) (LevelFrameComparison.targetProjection f n m hnm F) ≫
      (FrameRestriction.diagramIso f n m hnm F).hom = BoundedFrame.Diagram.augmentation F :=
  Relative.ResolutionAugmentation.diagramIso (G ⋙ QY) (LevelFrameComparison.sourceProjection f n m hnm F)
    (LevelFrameComparison.targetProjection f n m hnm F) (asIso (LevelFrameComparison.comparison f n m hnm F)) (LevelFrameComparison.projection f n m hnm F)

theorem augmentation : mappedAugmentation f n m hnm F ≫
    (FrameRestriction.presheafIso f n m hnm F).hom = BoundedFrame.Diagram.augmentation F :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (FrameRestriction.diagramIso f n m hnm F).hom)
      (restriction_augmentation f n m hnm F)).trans (diagram_augmentation f n m hnm F))

theorem mapped_zero : (mappedAugmentation f n m hnm F).f 0 =
    (Relative.ComplexRestriction.restriction (B := B) G).map
      (RelativeCrystalline.ModuleComplex.augmentationZero P QY π) :=
  Relative.RestrictionAugmentation.mappedAugmentation_zero G P QY π

theorem zero : (Relative.ComplexRestriction.restriction (B := B) G).map
    (RelativeCrystalline.ModuleComplex.augmentationZero P QY π) ≫
      (FrameRestriction.presheafIso f n m hnm F).hom.f 0 =
    RelativeCrystalline.ModuleComplex.augmentationZero (BoundedFrame.Diagram.productDiagram F) QX
      (BoundedFrame.Diagram.projection F) := by
  have h := congrArg (fun η => η.f 0) (augmentation f n m hnm F)
  have h₀ := mapped_zero f n m hnm F
  have h₁ := RelativeCrystalline.ModuleComplex.augmentation_zero (BoundedFrame.Diagram.productDiagram F) QX
    (BoundedFrame.Diagram.projection F)
  exact (congrArg (fun a => a ≫ (FrameRestriction.presheafIso f n m hnm F).hom.f 0) h₀).symm.trans
    (h.trans h₁)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameAugmentation
