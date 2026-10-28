import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCrystallineCup
import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarCupAlgebra

/-! # Rational Cup Algebra -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupAlgebra

noncomputable section

/-! Associativity and alternating degree-one products on the exact
original rational crystalline cohomology, including residue characteristic two. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCrystallineCup OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport

attribute [local irreducible] GradedCupTransport.degreeCast BalancedBounded.CechCup.cup

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

abbrev cohomology (i : ℕ) : Type (u + 2) := Witt.Crystalline.rationalCohomology p k X i

local notation "W" => WittVector p k
local notation "K" => FractionRing (WittVector p k)
local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X
local notation "H" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupAlgebra.cohomology p k X
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCrystallineCup.integralCup p k X hprojective
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCrystallineCup.cup p k X hprojective

private theorem integral_assoc (i j l : ℕ) (x : I i) (y : I j) (z : I l) :
    GradedCupTransport.degreeCast W I (Nat.add_assoc i j l) (μ (i + j) l (μ i j x y) z) =
      μ i (j + l) x (μ j l y z) := by
  simp only [RationalCrystallineCup.integralCup_apply]
  exact (ScalarCupAlgebra.degreeCast_changeRing (R := CR) I W (Nat.add_assoc i j l) _).trans
    (CupAlgebra.Integral.assoc p k X hprojective i j l x y z)

private theorem integral_one_add_swap (x y : I 1) : μ 1 1 x y + μ 1 1 y x = 0 := by
  simp only [RationalCrystallineCup.integralCup_apply]
  exact CupAlgebra.Integral.one_add_swap p k X hprojective x y

abbrev assoc (i j l : ℕ) (x : H i) (y : H j) (z : H l) := by
  have result := ScalarCupAlgebra.assoc K I μ (integral_assoc p k X hprojective) i j l x y z
  exact result

theorem one_add_swap (x y : H 1) : ν 1 1 x y + ν 1 1 y x = 0 :=
  ScalarCupAlgebra.one_add_swap K I μ (integral_one_add_swap p k X hprojective) x y

theorem self_eq_zero (x : H 1) : ν 1 1 x x = 0 := by
  have h2 : (2 : K) • ν 1 1 x x = 0 :=
    (two_smul K _).trans (one_add_swap p k X hprojective x x)
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupAlgebra
