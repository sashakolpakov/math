import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-!
# Shifted signed binomial coefficients

Multiplication by `(-X)^A` shifts the binomial coefficients by `A` and
multiplies them by the constant sign `(-1)^A`. The weighted-prefix identity
accounts for the vanishing coefficients below that shift.
-/

namespace SubexponentialSAT.Subexp.ScalarBinomial

open Polynomial
open scoped BigOperators

variable {K : Type*} [CommRing K]

theorem coeff_signed_binomial (A B j : ℕ) :
    (((-X : K[X]) ^ A) * (1 + X) ^ B).coeff j =
      if A ≤ j then (-1 : K) ^ A * (B.choose (j - A) : K) else 0 := by
  have hX : (-X : K[X]) = C (-1 : K) * X := by simp
  rw [hX, mul_pow, ← map_pow, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  simp only [coeff_one_add_X_pow]
  by_cases hj : A ≤ j <;> simp [hj]

theorem coeff_signed_binomial_add (A B k : ℕ) :
    (((-X : K[X]) ^ A) * (1 + X) ^ B).coeff (A + k) =
      (-1 : K) ^ A * (B.choose k : K) := by
  rw [coeff_signed_binomial, ite_eq_left (Nat.le_add_right A k), Nat.add_sub_cancel_left]

theorem weighted_prefix (a : ℕ → K) (A B R : ℕ) :
    (∑ j ∈ Finset.range R, a j * (((-X : K[X]) ^ A) * (1 + X) ^ B).coeff j) =
      (-1 : K) ^ A *
        ∑ k ∈ Finset.range (R - A), a (A + k) * (B.choose k : K) := by
  induction R with
  | zero => simp
  | succ R ih =>
      rw [Finset.sum_range_succ, ih, coeff_signed_binomial]
      by_cases h : A ≤ R
      · rw [ite_eq_left h, Nat.succ_sub h, Finset.sum_range_succ, mul_add,
          Nat.add_sub_of_le h]
        rw [mul_left_comm (a R) ((-1 : K) ^ A)]
      · have hlt : R < A := lt_of_not_ge h
        have hnext : R + 1 ≤ A := Nat.succ_le_of_lt hlt
        simp [h, Nat.sub_eq_zero_of_le hlt.le, Nat.sub_eq_zero_of_le hnext]

end SubexponentialSAT.Subexp.ScalarBinomial

end OAI.Algorithms
