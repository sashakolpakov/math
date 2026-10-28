import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.LevelFrameComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction

/-! # Frame Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameRestriction

noncomputable section

/-!
# IntegralComparison: the original bounded relative frame complex restricts to the lower level's native complex
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.LevelFrameComparison

universe u

variable {p : ℕ} {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) (n m : ℕ) (hnm : n ≤ m)
  [Fact p.Prime] [IsSeparated f]
  (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n

def restrictionIso :
    ((Relative.ComplexRestriction.restriction (B := B) G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (BoundedFrame.Diagram.complex ((G).obj F)) ≅
    RelativeCrystalline.ModuleComplex.complex (LevelFrameComparison.targetDiagram f n m hnm F) (G ⋙ QY)
      (LevelFrameComparison.targetProjection f n m hnm F) :=
  Relative.ComplexRestriction.complexIso G (BoundedFrame.Diagram.productDiagram ((G).obj F)) QY
    (BoundedFrame.Diagram.projection ((G).obj F))

def diagramIso :
    RelativeCrystalline.ModuleComplex.complex (LevelFrameComparison.targetDiagram f n m hnm F) (G ⋙ QY) (LevelFrameComparison.targetProjection f n m hnm F) ≅
      RelativeCrystalline.ModuleComplex.complex (LevelFrameComparison.sourceDiagram f n F) (G ⋙ QY) (LevelFrameComparison.sourceProjection f n m hnm F) :=
  Relative.ResolutionFunctor.diagramIso (G ⋙ QY) (LevelFrameComparison.sourceProjection f n m hnm F) (LevelFrameComparison.targetProjection f n m hnm F)
    (asIso (LevelFrameComparison.comparison f n m hnm F)) (LevelFrameComparison.projection f n m hnm F)

def presheafIso :
    ((Relative.ComplexRestriction.restriction (B := B) G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (BoundedFrame.Diagram.complex ((G).obj F)) ≅ BoundedFrame.Diagram.complex F :=
  restrictionIso f n m hnm F ≪≫ diagramIso f n m hnm F

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameRestriction
