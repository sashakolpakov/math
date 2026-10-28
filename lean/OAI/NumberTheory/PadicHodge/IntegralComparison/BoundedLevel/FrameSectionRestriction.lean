import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.FrameRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.RelativeFrame.DiagramChange

/-! # Frame Section Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSectionRestriction

noncomputable section

/-! The original presheaf frame section map is compatible with restriction between bounded levels. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.LevelFrameComparison

universe u

variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B] {J : Ideal B} {δ : DividedPowers J}
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of B)) [IsSeparated f]
  (n m : ℕ) (hnm : n ≤ m) (F : BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.LevelMaps.inclusion (p := p) (J := J) (δ := δ) f n m hnm
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f m
local notation "QX" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) f n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction.restriction (B := B) G

def sourceIso : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    (RelativeFrame.ComplexMap.constantComplex ((G).obj F).obj) ≅
      RelativeFrame.ComplexMap.constantComplex (C := BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n) F.obj :=
  RelativeFrame.FrameRestriction.sourceIso G ((G).obj F).obj

theorem presheaf : ((R).mapHomologicalComplex (ComplexShape.up ℕ)).map
    (RelativeFrame.ComplexMap.map (BoundedFrame.Diagram.productDiagram ((G).obj F)) QY
      (BoundedFrame.Diagram.projection ((G).obj F)) ((G).obj F).obj
        (BoundedFrame.Symbols.frameProjection ((G).obj F))) ≫
          (FrameRestriction.presheafIso f n m hnm F).hom =
    (sourceIso f n m hnm F).hom ≫ RelativeFrame.ComplexMap.map
      (BoundedFrame.Diagram.productDiagram F) QX (BoundedFrame.Diagram.projection F) F.obj
        (BoundedFrame.Symbols.frameProjection F) := by
  have h₁ := RelativeFrame.FrameRestriction.complexes G (BoundedFrame.Diagram.productDiagram ((G).obj F)) QY
    (BoundedFrame.Diagram.projection ((G).obj F)) ((G).obj F).obj (BoundedFrame.Symbols.frameProjection ((G).obj F))
  have h₂ := RelativeFrame.DiagramChange.complexes (LevelFrameComparison.sourceDiagram f n F) (LevelFrameComparison.targetDiagram f n m hnm F)
    (G ⋙ QY) (LevelFrameComparison.sourceProjection f n m hnm F) (LevelFrameComparison.targetProjection f n m hnm F) (LevelFrameComparison.comparison f n m hnm F)
    (LevelFrameComparison.projection f n m hnm F) ((G).obj F).obj (LevelFrameComparison.sourceFrameProjection f n m hnm F)
    (LevelFrameComparison.targetFrameProjection f n m hnm F) (LevelFrameComparison.frameProjection f n m hnm F)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun a => a ≫ (FrameRestriction.diagramIso f n m hnm F).hom) h₁).trans
      ((Category.assoc _ _ _).trans (congrArg (fun a => (sourceIso f n m hnm F).hom ≫ a) h₂)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedLevel.FrameSectionRestriction
