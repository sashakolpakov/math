import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCupLevel
import OAI.NumberTheory.PadicHodge.IntegralComparison.Cosimplicial.ExteriorNaturality

/-! # Witt Cup Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCupUnit

noncomputable section

/-! The coefficient-one class for the native smooth proper Witt cover
is compatible with every actual bounded restriction map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.SmoothProper.WittFrameFamily.Family

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]

local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "DP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "PIdeal" => Ideal.span {(p : WittVector p k)}

local instance separated : IsSeparated f := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

abbrev one (n : ℕ) := BalancedBounded.CupUnit.one p k (J := PIdeal) (δ := DP) f n
  (SmoothProper.WittFrameFamily.Family.frame p k X n) (SmoothProper.WittFrameCover.covering p k X n)

abbrev one_cup (n : ℕ) := BalancedBounded.CupUnit.one_cup p k (J := PIdeal) (δ := DP) f n
  (SmoothProper.WittFrameFamily.Family.frame p k X n) (SmoothProper.WittFrameCover.covering p k X n)

abbrev cup_one (n : ℕ) := BalancedBounded.CupUnit.cup_one p k (J := PIdeal) (δ := DP) f n
  (SmoothProper.WittFrameFamily.Family.frame p k X n) (SmoothProper.WittFrameCover.covering p k X n)

theorem transition (n m : ℕ) (hnm : n ≤ m) :
    Bounded.CohomologyTransition.map (p := p) (J := PIdeal) (δ := DP) f n m hnm 0
      (one p k X m) = one p k X n := by
  exact (WittCupLevel.equivalence_natural p k X n m hnm 0
    (Cosimplicial.ModuleCupAlgebra.cohomologyOne (SmoothProper.WittCechCup.cochainAlgebra p k X m))).symm.trans
    (congrArg (SmoothProperWittCup.equivalence p k X n 0)
      (Cosimplicial.ExteriorNaturality.Cup.cohomologyOne_natural
        (SmoothProper.WittCechCup.transition p k X n m hnm)))

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCupUnit
