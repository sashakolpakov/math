import OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackDiagram
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.DiagramComplexMap
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction
import OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.PostcomposeComplex

/-! # Pullback Complex -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackComplex.BoundedFramePullbackComplex

noncomputable section

/-! Actual relative crystalline complexes pull back along arbitrary geometric
maps and compatible frame morphisms, preserving the structure augmentation. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.BigCrystallineSite OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackDiagram.BoundedFramePullbackDiagram

universe u
variable {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
  {J : Ideal B} {δ : DividedPowers J} {X Y : Scheme.{u}}
  {f : X ⟶ Spec (CommRingCat.of B)} {fY : Y ⟶ Spec (CommRingCat.of B)}
  [IsSeparated f] [IsSeparated fY] (g : X ⟶ Y) (hg : g ≫ fY = f) (n : ℕ)
  (FX : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) f n)
  (FY : IntegralComparison.BoundedCrystalline.Site.Objects (p := p) (J := J) (δ := δ) fY n)

local notation "G" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n
local notation "QY" => OAI.NumberTheory.PadicHodge.IntegralComparison.BoundedCrystalline.Site.inclusion (p := p) (J := J) (δ := δ) fY n
local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Relative.ComplexRestriction.restriction (B := B)
  (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n)

variable (α : (IntegralComparison.BoundedOpen.Equivalence.postcompose (p := p) (J := J) (δ := δ) g hg n).obj FX ⟶ FY)

def diagramMap :
    IntegralComparison.RelativeCrystalline.ModuleComplex.complex (PullbackDiagram.BoundedFramePullbackDiagram.targetDiagram g hg n FY) (G ⋙ QY)
      (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY) ⟶
    IntegralComparison.RelativeCrystalline.ModuleComplex.complex (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX) (G ⋙ QY)
      (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX) :=
  IntegralComparison.Relative.DiagramComplexMap.map (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX) (PullbackDiagram.BoundedFramePullbackDiagram.targetDiagram g hg n FY)
    (G ⋙ QY) (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX) (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY)
    (PullbackDiagram.BoundedFramePullbackDiagram.comparison g hg n FX FY α) (PullbackDiagram.BoundedFramePullbackDiagram.projection g hg n FX FY α)

def postcomposeIso :
    IntegralComparison.RelativeCrystalline.ModuleComplex.complex (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX) (G ⋙ QY)
      (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX) ≅ IntegralComparison.BoundedFrame.Diagram.complex FX :=
  IntegralComparison.Relative.PostcomposeComplex.complexIso g hg (IntegralComparison.BoundedFrame.Diagram.productDiagram FX)
    (IntegralComparison.BoundedCrystalline.Site.inclusion f n) (IntegralComparison.BoundedFrame.Diagram.projection FX)

def map : ((R).mapHomologicalComplex (.up ℕ)).obj (IntegralComparison.BoundedFrame.Diagram.complex FY) ⟶
    IntegralComparison.BoundedFrame.Diagram.complex FX :=
  (IntegralComparison.Relative.ComplexRestriction.complexIso G (IntegralComparison.BoundedFrame.Diagram.productDiagram FY)
    QY (IntegralComparison.BoundedFrame.Diagram.projection FY)).hom ≫ diagramMap g hg n FX FY α ≫
      (postcomposeIso g hg n FX).hom

theorem augmentation_zero : (R).map ((IntegralComparison.BoundedFrame.Diagram.augmentation FY).f 0) ≫
    (BoundedFramePullbackComplex.map g hg n FX FY α).f 0 = (IntegralComparison.BoundedFrame.Diagram.augmentation FX).f 0 := by
  apply NatTrans.ext
  funext U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact IntegralComparison.Relative.DiagramComplexMap.constants (PullbackDiagram.BoundedFramePullbackDiagram.sourceDiagram g hg n FX) (PullbackDiagram.BoundedFramePullbackDiagram.targetDiagram g hg n FY)
    (G ⋙ QY) (PullbackDiagram.BoundedFramePullbackDiagram.sourceProjection g hg n FX) (PullbackDiagram.BoundedFramePullbackDiagram.targetProjection g hg n FY)
    (PullbackDiagram.BoundedFramePullbackDiagram.comparison g hg n FX FY α) (PullbackDiagram.BoundedFramePullbackDiagram.projection g hg n FX FY α) U.unop a

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.BoundedFrame.PullbackComplex.BoundedFramePullbackComplex
