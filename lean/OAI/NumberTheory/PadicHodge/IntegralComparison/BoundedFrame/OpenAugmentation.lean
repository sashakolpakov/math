import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.RestrictionAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeAugmentation
import OAI.NumberTheory.PadicHodge.IntegralComparison.AugmentationIsoComposition

/-! # Open Augmentation -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenAugmentation

noncomputable section

/-!
# IntegralComparison: the open-chart frame comparison preserves the original structure-presheaf augmentation
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Postcompose.Comparison

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) [Mono g] (hg : g ≫ fY = f) (n : ℕ)
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
      (Diagram.complex ((G).obj F)) :=
  (Relative.PostcomposeAugmentation.sourceIso g hg QX).inv ≫
    Relative.RestrictionAugmentation.mappedAugmentation G P QY π

omit [IsSeparated f] [Mono g] in
theorem restriction_augmentation : Relative.RestrictionAugmentation.mappedAugmentation G P QY π ≫
    (OpenRestriction.restrictionIso g hg n F).hom =
      RelativeCrystalline.ModuleComplex.augmentation (Postcompose.Comparison.targetDiagram g hg n F) (G ⋙ QY)
        (Postcompose.Comparison.targetProjection g hg n F) :=
  Relative.RestrictionAugmentation.augmentation G P QY π

theorem diagram_augmentation : RelativeCrystalline.ModuleComplex.augmentation
    (Postcompose.Comparison.targetDiagram g hg n F) (G ⋙ QY) (Postcompose.Comparison.targetProjection g hg n F) ≫
      (OpenRestriction.diagramIso g hg n F).hom =
    RelativeCrystalline.ModuleComplex.augmentation (Postcompose.Comparison.sourceDiagram g hg n F) (G ⋙ QY)
      (Postcompose.Comparison.sourceProjection g hg n F) :=
  Relative.ResolutionAugmentation.diagramIso (G ⋙ QY) (Postcompose.Comparison.sourceProjection g hg n F)
    (Postcompose.Comparison.targetProjection g hg n F) (asIso (Postcompose.Comparison.comparison g hg n F)) (Postcompose.Comparison.projection g hg n F)

omit [IsSeparated fY] [Mono g] in
theorem postcompose_augmentation : RelativeCrystalline.ModuleComplex.augmentation
    (Postcompose.Comparison.sourceDiagram g hg n F) (G ⋙ QY) (Postcompose.Comparison.sourceProjection g hg n F) ≫
      (OpenRestriction.postcomposeIso g hg n F).hom =
    (Relative.PostcomposeAugmentation.sourceIso g hg QX).hom ≫ Diagram.augmentation F :=
  Relative.PostcomposeAugmentation.augmentation g hg (Diagram.productDiagram F) QX
    (Diagram.projection F)

theorem augmentation : mappedAugmentation g hg n F ≫ (OpenRestriction.presheafIso g hg n F).hom =
    Diagram.augmentation F :=
  AugmentationIsoComposition.transport (Relative.PostcomposeAugmentation.sourceIso g hg QX)
    (OpenRestriction.restrictionIso g hg n F) (OpenRestriction.diagramIso g hg n F)
    (OpenRestriction.postcomposeIso g hg n F)
    (Relative.RestrictionAugmentation.mappedAugmentation G P QY π)
    (RelativeCrystalline.ModuleComplex.augmentation (Postcompose.Comparison.targetDiagram g hg n F) (G ⋙ QY) (Postcompose.Comparison.targetProjection g hg n F))
    (RelativeCrystalline.ModuleComplex.augmentation (Postcompose.Comparison.sourceDiagram g hg n F) (G ⋙ QY) (Postcompose.Comparison.sourceProjection g hg n F))
    (Diagram.augmentation F) (restriction_augmentation g hg n F)
    (diagram_augmentation g hg n F) (postcompose_augmentation g hg n F)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenAugmentation
