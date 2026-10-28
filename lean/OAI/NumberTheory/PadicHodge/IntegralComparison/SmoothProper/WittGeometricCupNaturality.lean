import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.GeometricCupNaturality
import OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricCup

/-! # Witt Geometric Cup Naturality -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricCupNaturality

noncomputable section

/-! The native bounded crystalline cup is natural for every genuine
morphism of smooth proper special fibres. The required frame refinement
is constructed from the actual geometric cover. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X Y : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  [IsProper Y.hom] [Smooth Y.hom] (g : X ⟶ Y) (n : ℕ)

local notation "WX" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "WY" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k Y
local notation "PIdeal" => Ideal.span {(p : WittVector p k)}
local notation "DP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "FX" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement.source p k X Y g n
local notation "hg" => OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricRefinement.over_witt p k X Y g

local instance sourceSeparated : IsSeparated WX := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

local instance targetSeparated : IsSeparated WY := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

theorem cup_natural (i j : ℕ)
    (x : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) WY n i)
    (y : BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) WY n j) :
    BoundedCrystalline.CrystallinePullback.pullback g.left hg n (i + j)
      (WittCechCup.cup p k Y n i j x y) =
        WittCechCup.cup p k X n i j
          (BoundedCrystalline.CrystallinePullback.pullback g.left hg n i x)
          (BoundedCrystalline.CrystallinePullback.pullback g.left hg n j y) := by
  have hn := Bounded.GeometricCupNaturality.cup_natural p k g.left hg n FX (WittFrameFamily.Family.frame p k Y n)
    (WittGeometricRefinement.targetIndex p k X Y g n)
    (WittGeometricRefinement.targetMap p k X Y g n)
    (WittGeometricRefinement.covering p k X Y g n)
    (WittFrameCover.covering p k Y n) i j x y
  exact hn.trans (Bounded.CupFamilyRefinement.Family.cup_eq p k WX n FX (WittFrameFamily.Family.frame p k X n) Sigma.fst
    (WittGeometricRefinement.sourceMap p k X Y g n)
    (WittGeometricRefinement.covering p k X Y g n)
    (WittFrameCover.covering p k X n) i j
    (BoundedCrystalline.CrystallinePullback.pullback g.left hg n i x)
    (BoundedCrystalline.CrystallinePullback.pullback g.left hg n j y))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittGeometricCupNaturality
