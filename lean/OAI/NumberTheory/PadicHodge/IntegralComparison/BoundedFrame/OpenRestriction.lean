import OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.Postcompose
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ResolutionFunctor
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeComplex

/-! # Open Restriction -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenRestriction

noncomputable section

/-!
# IntegralComparison: the original bounded relative frame complex restricts to the chart's native complex
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

def restrictionIso :
    ((Relative.ComplexRestriction.restriction (B := B) G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Diagram.complex ((G).obj F)) ≅
    RelativeCrystalline.ModuleComplex.complex (Postcompose.Comparison.targetDiagram g hg n F) (G ⋙ QY)
      (Postcompose.Comparison.targetProjection g hg n F) :=
  Relative.ComplexRestriction.complexIso G (Diagram.productDiagram ((G).obj F)) QY
    (Diagram.projection ((G).obj F))

def diagramIso :
    RelativeCrystalline.ModuleComplex.complex (Postcompose.Comparison.targetDiagram g hg n F) (G ⋙ QY) (Postcompose.Comparison.targetProjection g hg n F) ≅
      RelativeCrystalline.ModuleComplex.complex (Postcompose.Comparison.sourceDiagram g hg n F) (G ⋙ QY) (Postcompose.Comparison.sourceProjection g hg n F) :=
  Relative.ResolutionFunctor.diagramIso (G ⋙ QY) (Postcompose.Comparison.sourceProjection g hg n F) (Postcompose.Comparison.targetProjection g hg n F)
    (asIso (Postcompose.Comparison.comparison g hg n F)) (Postcompose.Comparison.projection g hg n F)

def postcomposeIso :
    RelativeCrystalline.ModuleComplex.complex (Postcompose.Comparison.sourceDiagram g hg n F) (G ⋙ QY) (Postcompose.Comparison.sourceProjection g hg n F) ≅
      Diagram.complex F :=
  Relative.PostcomposeComplex.complexIso g hg (Diagram.productDiagram F) QX
    (Diagram.projection F)

def presheafIso :
    ((Relative.ComplexRestriction.restriction (B := B) G).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (Diagram.complex ((G).obj F)) ≅ Diagram.complex F :=
  restrictionIso g hg n F ≪≫ diagramIso g hg n F ≪≫ postcomposeIso g hg n F

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedFrame.OpenRestriction
