import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.GeneralFrameComparison
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeComplex

/-! # Frame Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameRestriction

noncomputable section

/-!
# IntegralComparison: arbitrary geometric maps compare the original bounded relative frame complexes
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

def restrictionIso :
    ((Relative.ComplexRestriction.restriction (B := B) G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (BoundedFrame.Diagram.complex ((G).obj F)) ≅
    RelativeCrystalline.ModuleComplex.complex (GeneralFrameComparison.targetDiagram g hg n F) (G ⋙ QY)
      (GeneralFrameComparison.targetProjection g hg n F) :=
  Relative.ComplexRestriction.complexIso G (BoundedFrame.Diagram.productDiagram ((G).obj F)) QY
    (BoundedFrame.Diagram.projection ((G).obj F))

def diagramMap :
    RelativeCrystalline.ModuleComplex.complex (GeneralFrameComparison.targetDiagram g hg n F) (G ⋙ QY) (GeneralFrameComparison.targetProjection g hg n F) ⟶
      RelativeCrystalline.ModuleComplex.complex (GeneralFrameComparison.sourceDiagram g hg n F) (G ⋙ QY) (GeneralFrameComparison.sourceProjection g hg n F) :=
  Relative.DiagramComplexMap.map (GeneralFrameComparison.sourceDiagram g hg n F) (GeneralFrameComparison.targetDiagram g hg n F)
    (G ⋙ QY) (GeneralFrameComparison.sourceProjection g hg n F) (GeneralFrameComparison.targetProjection g hg n F)
    (GeneralFrameComparison.comparison g hg n F) (GeneralFrameComparison.projection g hg n F)

def postcomposeIso :
    RelativeCrystalline.ModuleComplex.complex (GeneralFrameComparison.sourceDiagram g hg n F) (G ⋙ QY) (GeneralFrameComparison.sourceProjection g hg n F) ≅
      BoundedFrame.Diagram.complex F :=
  Relative.PostcomposeComplex.complexIso g hg (BoundedFrame.Diagram.productDiagram F) QX
    (BoundedFrame.Diagram.projection F)

def presheafMap :
    ((Relative.ComplexRestriction.restriction (B := B) G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (BoundedFrame.Diagram.complex ((G).obj F)) ⟶ BoundedFrame.Diagram.complex F :=
  (restrictionIso g hg n F).hom ≫ diagramMap g hg n F ≫ (postcomposeIso g hg n F).hom

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedGeneral.FrameRestriction
