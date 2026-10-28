import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.Polynomial.Roots

/-! # Binomial Polynomials -/

namespace OAI.NumberTheory.Quaternion.Arithmetic.BinomialPolynomials

noncomputable section

/-! Polynomial interpolation of binomial coefficients and of powers
of a unipotent element over a characteristic-zero field. -/

open scoped Classical

variable {K : Type*} [Field K] [CharZero K]

def binomialCoefficientPolynomial (j : ℕ) : Polynomial K :=
  Polynomial.C ((j.factorial : K)⁻¹) * descPochhammer K j

theorem binomialCoefficientPolynomial_eval_nat (j m : ℕ) :
    (binomialCoefficientPolynomial (K := K) j).eval (m : K) = (m.choose j : K) := by
  rw [binomialCoefficientPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr j.factorial_ne_zero)]

theorem polynomial_eq_of_nat_evaluations (p q : Polynomial K)
    (h : ∀ m : ℕ, p.eval (m : K) = q.eval (m : K)) : p = q := by
  apply p.eq_of_infinite_eval_eq q
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R := K))).mono
  rintro x ⟨m, rfl⟩
  exact h m

variable {A : Type*} [Ring A] [Algebra K A]

omit [CharZero K] in
theorem nilpotent_binomial_sum_nat (N : A) (d : ℕ) (hd : N ^ d = 0) (m : ℕ) :
    (∑ j ∈ Finset.range d, (m.choose j : K) • N ^ j) = (1 + N) ^ m := by
  let f := fun j => (m.choose j : K) • N ^ j
  have hdmax : (∑ j ∈ Finset.range d, f j) = ∑ j ∈ Finset.range (max d (m + 1)), f j := by
    apply Finset.sum_subset (Finset.range_mono (le_max_left _ _))
    intro j _ hj
    have hdj : d ≤ j := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
    simp only [f, pow_eq_zero_of_le hdj hd, smul_zero]
  have hmmax : (∑ j ∈ Finset.range (m + 1), f j) = ∑ j ∈ Finset.range (max d (m + 1)), f j := by
    apply Finset.sum_subset (Finset.range_mono (le_max_right _ _))
    intro j _ hj
    have hmj : m < j := by
      have h := Nat.le_of_not_gt (fun h => hj (Finset.mem_range.mpr h))
      omega
    simp only [f, Nat.choose_eq_zero_of_lt hmj, Nat.cast_zero, zero_smul]
  rw [hdmax, ← hmmax]
  have hb := (Commute.one_right N).add_pow m
  simpa only [f, one_pow, mul_one, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, add_comm,
    Nat.cast_comm] using hb.symm

end

end OAI.NumberTheory.Quaternion.Arithmetic.BinomialPolynomials
