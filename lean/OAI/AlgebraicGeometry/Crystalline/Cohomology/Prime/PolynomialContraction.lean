import OAI.AlgebraicGeometry.Crystalline.Cohomology.Witt.PrimeWeightUnits
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.MonoidAlgebra.Module

/-! # Polynomial Contraction -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialContraction.PrimePolynomialContraction

noncomputable section

/-!
# Integral polynomial contraction away from weights divisible by p

Integration divides only by weights prime to p. The two residual
projections retain exponents divisible by p in degree zero and
exponents congruent to p - 1 in degree one. These are the polynomial
components through which Frobenius factors.
-/

open _root_.Polynomial

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] [CharP k p]

local notation "W" => WittVector p k

def operator (v : ℕ → W[X]) : W[X] →ₗ[W] W[X] :=
  (Finsupp.linearCombination W v).comp
    ((Polynomial.toFinsuppIsoLinear W).trans (AddMonoidAlgebra.coeffLinearEquiv W)).toLinearMap

omit [CharP k p] in
theorem operator_monomial (v : ℕ → W[X]) (n : ℕ) (a : W) :
    operator p k v (monomial n a) = a • v n := by
  change Finsupp.linearCombination W v (Finsupp.single n a) = a • v n
  exact Finsupp.linearCombination_single W a n

def primitive : W[X] →ₗ[W] W[X] :=
  operator p k (fun n => monomial (n + 1) (Witt.PrimeWeightUnits.WittPrimeWeightUnits.inverse p k (n + 1)))

def projection (ε : ℕ) : W[X] →ₗ[W] W[X] :=
  operator p k (fun n => if p ∣ n + ε then monomial n 1 else 0)

theorem primitive_monomial (n : ℕ) (a : W) :
    primitive p k (monomial n a) = monomial (n + 1) (a * Witt.PrimeWeightUnits.WittPrimeWeightUnits.inverse p k (n + 1)) := by
  rw [primitive, operator_monomial, Polynomial.smul_monomial, smul_eq_mul]

omit [CharP k p] in
theorem projection_monomial (ε n : ℕ) (a : W) :
    projection p k ε (monomial n a) = if p ∣ n + ε then monomial n a else 0 := by
  rw [projection, operator_monomial]
  by_cases h : p ∣ n + ε
  · simp [h, Polynomial.smul_monomial, smul_eq_mul]
  · simp [h]

theorem derivative_primitive :
    Polynomial.derivative.comp (primitive p k) + projection p k 1 = LinearMap.id := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  change Polynomial.derivative (primitive p k (monomial n a)) +
    projection p k 1 (monomial n a) = monomial n a
  rw [primitive_monomial, Polynomial.derivative_monomial_succ, projection_monomial,
    mul_assoc, ← Nat.cast_succ, Witt.PrimeWeightUnits.WittPrimeWeightUnits.inverse_mul]
  by_cases h : p ∣ n + 1 <;> simp [h]

theorem primitive_derivative :
    (primitive p k).comp Polynomial.derivative + projection p k 0 = LinearMap.id := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  change primitive p k (Polynomial.derivative (monomial n a)) +
    projection p k 0 (monomial n a) = monomial n a
  cases n with
  | zero =>
    rw [Polynomial.derivative_monomial, Nat.cast_zero, mul_zero, map_zero, map_zero, zero_add,
      projection_monomial]
    simp
  | succ n =>
    rw [Polynomial.derivative_monomial_succ, primitive_monomial, projection_monomial,
      Nat.add_zero, mul_assoc, ← Nat.cast_succ, Witt.PrimeWeightUnits.WittPrimeWeightUnits.mul_inverse]
    by_cases h : p ∣ n + 1 <;> simp [h]

theorem projection_commutes :
    Polynomial.derivative.comp (projection p k 0) = (projection p k 1).comp Polynomial.derivative := by
  have h₀ := congrArg (fun f : W[X] →ₗ[W] W[X] => Polynomial.derivative.comp f)
    (primitive_derivative p k)
  have h₁ := congrArg (fun f : W[X] →ₗ[W] W[X] => f.comp Polynomial.derivative)
    (derivative_primitive p k)
  simp only [LinearMap.comp_add, LinearMap.add_comp, LinearMap.comp_assoc,
    LinearMap.comp_id, LinearMap.id_comp] at h₀ h₁
  exact add_left_cancel (h₀.trans h₁.symm)

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialContraction.PrimePolynomialContraction
