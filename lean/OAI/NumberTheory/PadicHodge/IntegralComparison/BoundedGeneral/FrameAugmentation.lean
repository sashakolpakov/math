import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.RestrictionAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentationMapComposition

/-! # Frame Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameAugmentation

noncomputable section

/-!
# IntegralComparison: the arbitrary geometric frame comparison preserves the original structure-presheaf augmentation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.GeneralFrameComparison

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "P" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.productDiagram
  (CategoryTheory.Functor.obj (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n) F)
local notation "π" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Diagram.projection
  (CategoryTheory.Functor.obj (BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n) F)

def mappedAugmentation : (CochainComplex.single₀ _).obj (RelativeCrystalline.ModuleComplex.ambientPresheaf QX) ⟶
    ((Relative.ComplexRestriction.restriction (B := B) G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (BoundedFrame.Diagram.complex ((G).obj F)) :=
  (Relative.PostcomposeAugmentation.sourceIso g hg QX).inv ≫
    Relative.RestrictionAugmentation.mappedAugmentation G P QY π

omit [IsSeparated f] in
theorem restriction_augmentation : Relative.RestrictionAugmentation.mappedAugmentation G P QY π ≫
    (FrameRestriction.restrictionIso g hg n F).hom =
      RelativeCrystalline.ModuleComplex.augmentation (GeneralFrameComparison.targetDiagram g hg n F) (G ⋙ QY)
        (GeneralFrameComparison.targetProjection g hg n F) :=
  Relative.RestrictionAugmentation.augmentation G P QY π

theorem diagram_augmentation : RelativeCrystalline.ModuleComplex.augmentation
    (GeneralFrameComparison.targetDiagram g hg n F) (G ⋙ QY) (GeneralFrameComparison.targetProjection g hg n F) ≫
      FrameRestriction.diagramMap g hg n F =
    RelativeCrystalline.ModuleComplex.augmentation (GeneralFrameComparison.sourceDiagram g hg n F) (G ⋙ QY)
      (GeneralFrameComparison.sourceProjection g hg n F) :=
  Relative.DiagramComplexMap.augmentation (GeneralFrameComparison.sourceDiagram g hg n F) (GeneralFrameComparison.targetDiagram g hg n F)
    (G ⋙ QY) (GeneralFrameComparison.sourceProjection g hg n F) (GeneralFrameComparison.targetProjection g hg n F)
    (GeneralFrameComparison.comparison g hg n F) (GeneralFrameComparison.projection g hg n F)

omit [IsSeparated fY] in
theorem postcompose_augmentation : RelativeCrystalline.ModuleComplex.augmentation
    (GeneralFrameComparison.sourceDiagram g hg n F) (G ⋙ QY) (GeneralFrameComparison.sourceProjection g hg n F) ≫
      (FrameRestriction.postcomposeIso g hg n F).hom =
    (Relative.PostcomposeAugmentation.sourceIso g hg QX).hom ≫ BoundedFrame.Diagram.augmentation F :=
  Relative.PostcomposeAugmentation.augmentation g hg (BoundedFrame.Diagram.productDiagram F) QX
    (BoundedFrame.Diagram.projection F)

theorem augmentation : mappedAugmentation g hg n F ≫ FrameRestriction.presheafMap g hg n F =
    BoundedFrame.Diagram.augmentation F :=
  AugmentationMapComposition.transport (Relative.PostcomposeAugmentation.sourceIso g hg QX)
    (FrameRestriction.restrictionIso g hg n F).hom (FrameRestriction.diagramMap g hg n F)
    (FrameRestriction.postcomposeIso g hg n F).hom
    (Relative.RestrictionAugmentation.mappedAugmentation G P QY π)
    (RelativeCrystalline.ModuleComplex.augmentation (GeneralFrameComparison.targetDiagram g hg n F) (G ⋙ QY) (GeneralFrameComparison.targetProjection g hg n F))
    (RelativeCrystalline.ModuleComplex.augmentation (GeneralFrameComparison.sourceDiagram g hg n F) (G ⋙ QY) (GeneralFrameComparison.sourceProjection g hg n F))
    (BoundedFrame.Diagram.augmentation F) (restriction_augmentation g hg n F)
    (diagram_augmentation g hg n F) (postcompose_augmentation g hg n F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameAugmentation
