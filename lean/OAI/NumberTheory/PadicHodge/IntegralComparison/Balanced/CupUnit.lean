import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.WittCupUnit

/-! # Cup Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupUnit.Integral

noncomputable section

/-! The compatible native finite-Witt coefficient-one classes give a
genuine unit in the original integral crystalline Ext cohomology. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CrystallineCup.Integral

attribute [local irreducible] GradedCupTransport.degreeCast BalancedBounded.CechCup.cup

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "R" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X
local notation "f" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.wittStructureMap p k X
local notation "DP" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k
local notation "PIdeal" => Ideal.span {(p : WittVector p k)}
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CrystallineCup.Integral.cup p k X hprojective

def compatibleOne : CrystallineCup.Integral.Compatible p k X 0 :=
  ⟨WittCupUnit.one p k X, by
    apply (Crystalline.CohomologyDifference.mem_compatible f 0 _).mpr
    intro n
    rw [Crystalline.InverseTransitionCoordinates.transition]
    exact WittCupUnit.transition p k X n (n + 1) (Nat.le_succ n)⟩

def one : H 0 := (CrystallineCup.Integral.equivalence p k X hprojective 0).symm (compatibleOne p k X)

theorem restriction_one (n : ℕ) :
    CrystallineCup.Integral.restriction p k X n 0 (one p k X hprojective) = WittCupUnit.one p k X n := by
  have h := (CrystallineCup.Integral.equivalence p k X hprojective 0).apply_symm_apply (compatibleOne p k X)
  exact (CrystallineCup.Integral.equivalence_coordinate p k X hprojective 0 n (one p k X hprojective)).symm.trans
    (congrArg (fun z : CrystallineCup.Integral.Compatible p k X 0 => z.val n) h)

theorem one_cup (i : ℕ) (x : H i) :
    GradedCupTransport.degreeCast R H (Nat.zero_add i) (μ 0 i (one p k X hprojective) x) = x :=
  GradedCupUnit.detected_left R H μ (one p k X hprojective)
    (fun n => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n)
    (CrystallineCup.Integral.restriction p k X) (CupAlgebra.Integral.ext p k X hprojective)
    (SmoothProperWittCup.cup p k X) (CrystallineCup.Integral.restriction_cup p k X hprojective)
    (WittCupUnit.one p k X) (restriction_one p k X hprojective)
    (WittCupUnit.one_cup p k X) i x

theorem cup_one (i : ℕ) (x : H i) : μ i 0 x (one p k X hprojective) = x :=
  GradedCupUnit.detected_right R H μ (one p k X hprojective)
    (fun n => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n)
    (CrystallineCup.Integral.restriction p k X) (CupAlgebra.Integral.ext p k X hprojective)
    (SmoothProperWittCup.cup p k X) (CrystallineCup.Integral.restriction_cup p k X hprojective)
    (WittCupUnit.one p k X) (restriction_one p k X hprojective)
    (WittCupUnit.cup_one p k X) i x

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupUnit.Integral
