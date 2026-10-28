import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupUnit
import OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupAlgebra
import OAI.NumberTheory.PadicHodge.IntegralComparison.ScalarGradedCupData

/-! # Rational Cup Unit -/

namespace OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupUnit

noncomputable section

/-! The balanced product on original rational crystalline cohomology
is a genuine unital graded algebra with alternating degree-one cup. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCrystallineCup OAI.NumberTheory.PadicHodge.IntegralComparison.GradedCupTransport

attribute [local irreducible] GradedCupTransport.degreeCast

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [Fintype k] [CharP k p]
  (X : Over (Spec (CommRingCat.of k))) [IsProper X.hom] [Smooth X.hom]
  (hprojective : Projectivity.Construction.ProjectiveOver k X.hom)

local notation "W" => WittVector p k
local notation "K" => FractionRing (WittVector p k)
local notation "CR" => OAI.NumberTheory.PadicHodge.IntegralComparison.Crystalline.ExactRestriction.Coeff (B := WittVector p k)
local notation "I" => OAI.NumberTheory.PadicHodge.IntegralComparison.Witt.Crystalline.integralCohomology p k X
local notation "V" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupAlgebra.cohomology p k X
local notation "μ" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCrystallineCup.integralCup p k X hprojective
local notation "ν" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCrystallineCup.cup p k X hprojective
local notation "oneI" => OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.CupUnit.Integral.one p k X hprojective

def one : V 0 := (1 : K) ⊗ₜ[W] oneI

private theorem integral_one_cup (i : ℕ) (x : I i) :
    GradedCupTransport.degreeCast W I (Nat.zero_add i) (μ 0 i oneI x) = x := by
  rw [RationalCrystallineCup.integralCup_apply]
  exact (ScalarCupAlgebra.degreeCast_changeRing (R := CR) I W (Nat.zero_add i) _).trans
    (CupUnit.Integral.one_cup p k X hprojective i x)

private theorem integral_cup_one (i : ℕ) (x : I i) : μ i 0 x oneI = x := by
  rw [RationalCrystallineCup.integralCup_apply]
  exact CupUnit.Integral.cup_one p k X hprojective i x

abbrev one_cup (i : ℕ) (x : V i) := by
  have result := GradedCupUnit.scalar_left W I μ oneI K (integral_one_cup p k X hprojective) i x
  exact result

abbrev cup_one (i : ℕ) (x : V i) := by
  have result := BilinearScalarExtension.map_right_unit K (μ i 0) oneI
    (integral_cup_one p k X hprojective i) x
  exact result

theorem scalarLeft : ∀ i (x : K ⊗[W] I i),
    GradedCupTransport.degreeCast K (fun i => K ⊗[W] I i) (Nat.zero_add i)
      (BilinearScalarExtension.map K (μ 0 i) ((1 : K) ⊗ₜ[W] oneI) x) = x :=
  GradedCupUnit.scalar_left W I μ oneI K (integral_one_cup p k X hprojective)

theorem scalarRight : ∀ i (x : K ⊗[W] I i),
    BilinearScalarExtension.map K (μ i 0) x ((1 : K) ⊗ₜ[W] oneI) = x :=
  fun i => BilinearScalarExtension.map_right_unit K (μ i 0) oneI
    (integral_cup_one p k X hprojective i)

private theorem integralAssoc (i j l : ℕ) (x : I i) (y : I j) (z : I l) :
    GradedCupTransport.degreeCast W I (Nat.add_assoc i j l) (μ (i + j) l (μ i j x y) z) =
      μ i (j + l) x (μ j l y z) := by
  simp only [RationalCrystallineCup.integralCup_apply]
  exact (ScalarCupAlgebra.degreeCast_changeRing (R := CR) I W (Nat.add_assoc i j l) _).trans
    (CupAlgebra.Integral.assoc p k X hprojective i j l x y z)

theorem scalarAssoc : ∀ i j l (x : K ⊗[W] I i) (y : K ⊗[W] I j) (z : K ⊗[W] I l),
    GradedCupTransport.degreeCast K (fun i => K ⊗[W] I i) (Nat.add_assoc i j l)
      (BilinearScalarExtension.map K (μ (i + j) l)
        (BilinearScalarExtension.map K (μ i j) x y) z) =
      BilinearScalarExtension.map K (μ i (j + l)) x
        (BilinearScalarExtension.map K (μ j l) y z) :=
  ScalarCupAlgebra.assoc K I μ (integralAssoc p k X hprojective)

theorem scalarSquare (x : K ⊗[W] I 1) :
    BilinearScalarExtension.map K (μ 1 1) x x = 0 := by
  have h2 : (2 : K) • BilinearScalarExtension.map K (μ 1 1) x x = 0 :=
    (two_smul K _).trans (ScalarCupAlgebra.one_add_swap K I μ
      (fun a b => by
        simp only [RationalCrystallineCup.integralCup_apply]
        exact CupAlgebra.Integral.one_add_swap p k X hprojective a b) x x)
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

def data := ScalarGradedCupData.data K I μ oneI
  (scalarLeft p k X hprojective) (scalarRight p k X hprojective)
  (scalarAssoc p k X hprojective) (scalarSquare p k X hprojective)

end

end OAI.NumberTheory.PadicHodge.IntegralComparison.Balanced.RationalCupUnit
