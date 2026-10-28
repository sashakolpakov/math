import OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialContraction

/-! # Polynomial Frobenius Weights -/

namespace OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights

noncomputable section

/-!
# Polynomial Frobenius weights and their integral retractions

Weight is exponent in degree zero and exponent plus one in degree one.
Multiplication of weights by p has an integral inverse on the retained
weight summands. These maps will give the Frobenius and transfer maps.
-/

open _root_.Polynomial

open OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialContraction.PrimePolynomialContraction

universe u

variable (p : ℕ) [Fact p.Prime]

def raiseIndex (ε n : ℕ) : ℕ := p * (n + ε) - ε
def lowerIndex (ε n : ℕ) : ℕ := (n + ε) / p - ε

theorem raiseIndex_add (ε n : ℕ) : raiseIndex p ε n + ε = p * (n + ε) := by
  apply Nat.sub_add_cancel
  have hp : 1 ≤ p := Nat.Prime.one_lt (Fact.out : p.Prime) |>.le
  have hm := Nat.mul_le_mul_right (n + ε) hp
  omega

theorem raiseIndex_dvd (ε n : ℕ) : p ∣ raiseIndex p ε n + ε := by
  rw [raiseIndex_add]
  exact dvd_mul_right p (n + ε)

theorem lower_raiseIndex (ε n : ℕ) : lowerIndex p ε (raiseIndex p ε n) = n := by
  unfold lowerIndex
  rw [raiseIndex_add, Nat.mul_div_cancel_left _ (Nat.Prime.pos (Fact.out : p.Prime)), Nat.add_sub_cancel]

omit [Fact p.Prime] in
theorem raise_lowerIndex (ε n : ℕ) (hε : ε ≤ 1) (h : p ∣ n + ε) :
    raiseIndex p ε (lowerIndex p ε n) = n := by
  have hq : ε ≤ (n + ε) / p := by
    by_cases he : ε = 0
    · subst ε; exact Nat.zero_le _
    · have he : ε = 1 := by omega
      subst ε
      by_contra hn
      have hz : (n + 1) / p = 0 := Nat.eq_zero_of_not_pos hn
      have hm := Nat.mul_div_cancel' h
      rw [hz, mul_zero] at hm
      omega
  unfold raiseIndex lowerIndex
  rw [Nat.sub_add_cancel hq, Nat.mul_div_cancel' h, Nat.add_sub_cancel]

variable (k : Type u) [Field k]

local notation "W" => WittVector p k

def raise (ε : ℕ) : W[X] →ₗ[W] W[X] :=
  PolynomialContraction.PrimePolynomialContraction.operator p k (fun n => monomial (raiseIndex p ε n) 1)

def lower (ε : ℕ) : W[X] →ₗ[W] W[X] :=
  PolynomialContraction.PrimePolynomialContraction.operator p k (fun n => if p ∣ n + ε then monomial (lowerIndex p ε n) 1 else 0)

theorem raise_monomial (ε n : ℕ) (a : W) :
    raise p k ε (monomial n a) = monomial (raiseIndex p ε n) a := by
  rw [raise, PolynomialContraction.PrimePolynomialContraction.operator_monomial, Polynomial.smul_monomial, smul_eq_mul, mul_one]

theorem lower_monomial (ε n : ℕ) (a : W) :
    lower p k ε (monomial n a) = if p ∣ n + ε then monomial (lowerIndex p ε n) a else 0 := by
  rw [lower, PolynomialContraction.PrimePolynomialContraction.operator_monomial]
  by_cases h : p ∣ n + ε
  · simp [h, Polynomial.smul_monomial, smul_eq_mul]
  · simp [h]

theorem lower_raise (ε : ℕ) : (lower p k ε).comp (raise p k ε) = LinearMap.id := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  change lower p k ε (raise p k ε (monomial n a)) = monomial n a
  rw [raise_monomial, lower_monomial, ite_eq_left (raiseIndex_dvd p ε n), lower_raiseIndex]

theorem raise_lower (ε : ℕ) (hε : ε ≤ 1) :
    (raise p k ε).comp (lower p k ε) = PolynomialContraction.PrimePolynomialContraction.projection p k ε := by
  apply Polynomial.lhom_ext'
  intro n
  apply LinearMap.ext
  intro a
  change raise p k ε (lower p k ε (monomial n a)) = PolynomialContraction.PrimePolynomialContraction.projection p k ε (monomial n a)
  rw [lower_monomial, PolynomialContraction.PrimePolynomialContraction.projection_monomial]
  by_cases h : p ∣ n + ε
  · rw [ite_eq_left h, raise_monomial, raise_lowerIndex p ε n hε h, ite_eq_left h]
  · rw [ite_eq_right h, map_zero, ite_eq_right h]

end

end OAI.AlgebraicGeometry.Crystalline.Cohomology.Prime.PolynomialFrobeniusWeights.PrimePolynomialFrobeniusWeights
