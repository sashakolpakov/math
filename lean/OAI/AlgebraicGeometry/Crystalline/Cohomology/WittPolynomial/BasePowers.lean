import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers
import OAI.AlgebraicGeometry.Crystalline.Cohomology.PD.GeneratorTransfer
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.DividedPowers.DPMorphism

/-! # Base Powers -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.BasePowers.WittPolynomialBasePowers

noncomputable section

/-!
# The base divided powers on Witt polynomial algebras

The actual polynomial ideal (p) inherits the specified Witt divided
powers. Positive divided powers of its generator are lifted integrally
from W(k); the generator-transfer theorem constructs all operations.
-/

universe u

variable (p : ℕ) [Fact p.Prime] (k σ : Type u) [Field k] [CharP k p]

local notation "W" => WittVector p k
local notation "K₀" => FractionRing W
local notation "P" => MvPolynomial σ W
local notation "Q" => MvPolynomial σ K₀
local notation "δ" => OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.DividedPowers.WittDividedPowers.wittDividedPowers p k

def ideal : Ideal P := Ideal.span {(p : P)}

def rationalMap : P →+* Q := MvPolynomial.map (algebraMap W K₀)

omit [CharP k p] in
theorem rationalMap_injective : Function.Injective (rationalMap p k σ) :=
  MvPolynomial.map_injective (algebraMap W K₀) (IsFractionRing.injective W K₀)

def rationalPowers : DividedPowers (⊤ : Ideal Q) := by
  classical
  exact DividedPowers.RatAlgebra.dividedPowers ⊤

omit [CharP k p] in
theorem base_ideal : (Ideal.span {(p : W)}).map (MvPolynomial.C : W →+* P) = ideal p k σ := by
  rw [ideal, Ideal.map_span, Set.image_singleton, map_natCast]

theorem base_dpow (n : ℕ) (x : W) (hx : x ∈ Ideal.span {(p : W)}) :
    rationalMap p k σ (MvPolynomial.C ((δ).dpow n x)) =
      (rationalPowers p k σ).dpow n (rationalMap p k σ (MvPolynomial.C x)) := by
  apply mul_left_cancel₀ (show (n.factorial : Q) ≠ 0 from Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  calc
    _ = rationalMap p k σ (MvPolynomial.C ((n.factorial : W) * (δ).dpow n x)) := by
      simp only [map_mul, map_natCast]
    _ = rationalMap p k σ (MvPolynomial.C (x ^ n)) :=
      congrArg (fun w => rationalMap p k σ (MvPolynomial.C w)) ((δ).factorial_mul_dpow_eq_pow hx)
    _ = (rationalMap p k σ (MvPolynomial.C x)) ^ n := by simp only [map_pow]
    _ = _ := ((rationalPowers p k σ).factorial_mul_dpow_eq_pow (Submodule.mem_top)).symm

theorem generator_lifts : ∀ s ∈ ({(p : P)} : Set P), ∀ n : ℕ, n ≠ 0 →
    ∃ y ∈ ideal p k σ, rationalMap p k σ y = (rationalPowers p k σ).dpow n (rationalMap p k σ s) := by
  rintro s (rfl : s = (p : P)) n hn
  have hp : (p : W) ∈ Ideal.span {(p : W)} := Ideal.subset_span (Set.mem_singleton _)
  refine ⟨MvPolynomial.C ((δ).dpow n (p : W)), ?_, ?_⟩
  · rw [← base_ideal]
    exact Ideal.mem_map_of_mem MvPolynomial.C ((δ).dpow_mem hn hp)
  · simpa only [map_natCast] using base_dpow p k σ n (p : W) hp

theorem ideal_map_eq_top : (ideal p k σ).map (rationalMap p k σ) = ⊤ := by
  rw [ideal, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_eq_top]
  have hp : IsUnit (p : K₀) := isUnit_iff_ne_zero.mpr
    (Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero (Fact.out : p.Prime)))
  simpa only [map_natCast] using hp.map (MvPolynomial.C : K₀ →+* Q)

def dividedPowers : DividedPowers (ideal p k σ) :=
  PD.GeneratorTransfer.PDGeneratorTransfer.dividedPowers (⊤ : Ideal Q) (rationalPowers p k σ) (rationalMap p k σ)
    {(p : P)} (generator_lifts p k σ) (rationalMap_injective p k σ) (ideal_map_eq_top p k σ)

theorem map_dpow (n : ℕ) (x : P) (hx : x ∈ ideal p k σ) :
    rationalMap p k σ ((WittPolynomialBasePowers.dividedPowers p k σ).dpow n x) =
      (rationalPowers p k σ).dpow n (rationalMap p k σ x) :=
  PD.GeneratorTransfer.PDGeneratorTransfer.map_dpow (⊤ : Ideal Q) (rationalPowers p k σ) (rationalMap p k σ)
    {(p : P)} (generator_lifts p k σ) (rationalMap_injective p k σ) (ideal_map_eq_top p k σ) n hx

theorem base_isDPMorphism : DividedPowers.IsDPMorphism δ (WittPolynomialBasePowers.dividedPowers p k σ)
    (algebraMap W P) where
  ideal_comp := (base_ideal p k σ).le
  dpow_comp {n} x hx := by
    apply rationalMap_injective p k σ
    have hx' : MvPolynomial.C x ∈ ideal p k σ := by
      rw [← base_ideal]
      exact Ideal.mem_map_of_mem MvPolynomial.C hx
    change rationalMap p k σ ((WittPolynomialBasePowers.dividedPowers p k σ).dpow n (MvPolynomial.C x)) =
      rationalMap p k σ (MvPolynomial.C ((δ).dpow n x))
    rw [map_dpow p k σ n _ hx']
    exact (base_dpow p k σ n x hx).symm

theorem ringMap_isDPMorphism (f : P →+* P) :
    DividedPowers.IsDPMorphism (WittPolynomialBasePowers.dividedPowers p k σ) (WittPolynomialBasePowers.dividedPowers p k σ) f where
  ideal_comp := by rw [ideal, Ideal.map_span, Set.image_singleton, map_natCast]
  dpow_comp {n} x hx := by
    symm
    have hx' : f x ∈ ideal p k σ := by
      have hf : (ideal p k σ).map f = ideal p k σ := by
        rw [ideal, Ideal.map_span, Set.image_singleton, map_natCast]
      rw [← hf]
      exact Ideal.mem_map_of_mem f hx
    apply mul_left_cancel₀ (show (n.factorial : P) ≠ 0 from Nat.cast_ne_zero.mpr n.factorial_ne_zero)
    calc
      _ = f ((n.factorial : P) * (WittPolynomialBasePowers.dividedPowers p k σ).dpow n x) := by rw [f.map_mul, map_natCast]
      _ = f (x ^ n) := congrArg f ((WittPolynomialBasePowers.dividedPowers p k σ).factorial_mul_dpow_eq_pow hx)
      _ = (f x) ^ n := f.map_pow x n
      _ = _ := ((WittPolynomialBasePowers.dividedPowers p k σ).factorial_mul_dpow_eq_pow hx').symm

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.WittPolynomial.BasePowers.WittPolynomialBasePowers
