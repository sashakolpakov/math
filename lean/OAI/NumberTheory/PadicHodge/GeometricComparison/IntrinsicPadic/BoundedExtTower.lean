import OAI.NumberTheory.PadicHodge.IntegralComparison.Bounded.CohomologyTransition
import OAI.NumberTheory.PadicHodge.IntegralComparison.SequentialKernelLimit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline
import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers

/-! # Bounded Ext Tower -/

namespace OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.BoundedExtTower.IntrinsicPadicBoundedExtTower

noncomputable section

/-! The inverse sequence formed directly from original bounded
crystalline Ext groups and their original successor restriction maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry Opposite

variable (p : ℕ) [Fact p.Prime] (Y : Over (Spec (CommRingCat.of (ZMod p))))

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p (ZMod p))
local notation "w" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p (ZMod p) Y

def diagram : ℕᵒᵖ ⥤ ModuleCat.{2} R :=
  IntegralComparison.SequentialKernelLimit.diagram R
    (fun n => IntegralComparison.BoundedCrystalline.CrystallineCohomology.Cohomology (p := p)
      (J := Ideal.span {(p : WittVector p (ZMod p))})
      (δ := AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p (ZMod p)) w n 1)
    (fun n => IntegralComparison.Bounded.CohomologyTransition.map w n (n + 1) (Nat.le_succ n) 1)

end

end OAI.NumberTheory.PadicHodge.GeometricComparison.IntrinsicPadic.BoundedExtTower.IntrinsicPadicBoundedExtTower
