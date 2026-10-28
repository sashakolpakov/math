import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusWeights

/-! # Polynomial Frobenius Differential -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusDifferential.PrimePolynomialFrobeniusDifferential

noncomputable section

/-! # Frobenius weight maps and the actual polynomial derivative -/

open _root_.Polynomial

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights

universe u

variable (p : ℕ) [Fact p.Prime] (k : Type u) [Field k]

local notation "W" => WittVector p k

theorem derivative_raise : Polynomial.derivative.comp (PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raise p k 0) =
    (p : W) • ((PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raise p k 1).comp Polynomial.derivative) := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  change Polynomial.derivative (PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raise p k 0 (monomial n a)) =
    (p : W) • PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raise p k 1 (Polynomial.derivative (monomial n a))
  cases n with
  | zero =>
    rw [PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raise_monomial]
    change Polynomial.derivative (monomial 0 a) = (p : W) • PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raise p k 1 (Polynomial.derivative (monomial 0 a))
    simp only [Polynomial.derivative_monomial, Nat.cast_zero, mul_zero, map_zero, smul_zero]
  | succ n =>
    rw [PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raise_monomial, Polynomial.derivative_monomial, Polynomial.derivative_monomial_succ,
      PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raise_monomial, Polynomial.smul_monomial]
    simp only [PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.raiseIndex, Nat.add_zero, Nat.sub_zero, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, smul_eq_mul]
    congr 1
    ring

theorem lower_derivative : (PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lower p k 1).comp Polynomial.derivative =
    (p : W) • (Polynomial.derivative.comp (PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lower p k 0)) := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  change PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lower p k 1 (Polynomial.derivative (monomial n a)) =
    (p : W) • Polynomial.derivative (PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lower p k 0 (monomial n a))
  cases n with
  | zero =>
    rw [PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lower_monomial]
    simp only [Nat.zero_add, dvd_zero, ite_true, PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lowerIndex, Nat.zero_div, Nat.sub_zero,
      Polynomial.derivative_monomial, Nat.cast_zero, mul_zero,
      map_zero, smul_zero]
  | succ n =>
    rw [Polynomial.derivative_monomial_succ, PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lower_monomial, PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lower_monomial, Nat.add_zero]
    by_cases h : p ∣ n + 1
    · rw [ite_eq_left h, ite_eq_left h, Polynomial.derivative_monomial, Polynomial.smul_monomial]
      simp only [PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights.lowerIndex, Nat.add_zero, Nat.sub_zero, smul_eq_mul]
      congr 1
      have hw : (p : W) * (((n + 1) / p : ℕ) : W) = ((n + 1 : ℕ) : W) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' h]
      calc
        a * ((n : W) + 1) = a * ((n + 1 : ℕ) : W) := by rw [Nat.cast_add, Nat.cast_one]
        _ = (p : W) * (a * (((n + 1) / p : ℕ) : W)) := by rw [← hw]; ring
    · rw [ite_eq_right h, ite_eq_right h, map_zero, smul_zero]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusDifferential.PrimePolynomialFrobeniusDifferential
