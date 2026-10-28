import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CrystallineCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.BalancedBounded.CupAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupDetection

/-! # Cup Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupAlgebra.Integral

noncomputable section

/-! Associativity and integral degree-one anticommutativity on the
original crystalline Ext groups, detected at the actual bounded levels. -/

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

local instance separated : IsSeparated f := by
  dsimp only [Witt.Crystalline.wittStructureMap]
  infer_instance

private abbrev bounded_assoc (n : ℕ) :=
  BalancedBounded.CupAlgebra.assoc p k (J := PIdeal) (δ := DP) f n
    (SmoothProper.WittFrameFamily.Family.frame p k X n)
    (SmoothProper.WittFrameCover.covering p k X n)

private abbrev bounded_one_add_swap (n : ℕ) :=
  BalancedBounded.CupAlgebra.one_add_swap p k (J := PIdeal) (δ := DP) f n
    (SmoothProper.WittFrameFamily.Family.frame p k X n)
    (SmoothProper.WittFrameCover.covering p k X n)

include hprojective in
theorem ext (i : ℕ) {x y : H i}
    (h : ∀ n, CrystallineCup.Integral.restriction p k X n i x = CrystallineCup.Integral.restriction p k X n i y) : x = y := by
  apply (CrystallineCup.Integral.equivalence p k X hprojective i).injective
  apply Subtype.ext
  funext n
  exact (CrystallineCup.Integral.equivalence_coordinate p k X hprojective i n x).trans
    ((h n).trans (CrystallineCup.Integral.equivalence_coordinate p k X hprojective i n y).symm)

theorem assoc (i j l : ℕ) (x : H i) (y : H j) (z : H l) :
    GradedCupTransport.degreeCast R H (Nat.add_assoc i j l) (μ (i + j) l (μ i j x y) z) =
      μ i (j + l) x (μ j l y z) :=
  GradedCupDetection.assoc R H
    (fun n => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n)
    (CrystallineCup.Integral.restriction p k X) (Integral.ext p k X hprojective) μ (SmoothProperWittCup.cup p k X)
    (CrystallineCup.Integral.restriction_cup p k X hprojective) (bounded_assoc p k X) i j l x y z

theorem one_add_swap (x y : H 1) : μ 1 1 x y + μ 1 1 y x = 0 :=
  GradedCupDetection.one_add_swap R H
    (fun n => BoundedCrystalline.CrystallineCohomology.Cohomology (p := p) (J := PIdeal) (δ := DP) f n)
    (CrystallineCup.Integral.restriction p k X) (Integral.ext p k X hprojective) μ (SmoothProperWittCup.cup p k X)
    (CrystallineCup.Integral.restriction_cup p k X hprojective) (bounded_one_add_swap p k X) x y

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupAlgebra.Integral
