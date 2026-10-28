import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.UnitNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCupUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittGeometricCup

/-! # Witt Unit Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittUnitNaturality

noncomputable section

/-! Actual geometric pullback preserves the genuine unit on each
smooth proper Witt crystalline level. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y) (n : ℕ)

local notation "WX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "WY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "FX" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement.source p k X Y g n
local notation "hg" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement.over_witt p k X Y g

local instance sourceSeparated : IsSeparated WX := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance targetSeparated : IsSeparated WY := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem one_natural : BoundedCrystalline.CrystallinePullback.pullback g.left hg n 0
      (WittCupUnit.one p k Y n) = WittCupUnit.one p k X n :=
  (BalancedBounded.UnitNaturality.pullback p k g.left hg n FX (SmoothProper.WittFrameFamily.Family.frame p k Y n)
    (SmoothProper.WittGeometricRefinement.targetIndex p k X Y g n)
    (SmoothProper.WittGeometricRefinement.targetMap p k X Y g n)
    (SmoothProper.WittGeometricRefinement.covering p k X Y g n)
    (SmoothProper.WittFrameCover.covering p k Y n)).trans
    (BalancedBounded.UnitNaturality.refinement p k WX n FX (SmoothProper.WittFrameFamily.Family.frame p k X n) Sigma.fst
      (SmoothProper.WittGeometricRefinement.sourceMap p k X Y g n)
      (SmoothProper.WittGeometricRefinement.covering p k X Y g n)
      (SmoothProper.WittFrameCover.covering p k X n))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittUnitNaturality
