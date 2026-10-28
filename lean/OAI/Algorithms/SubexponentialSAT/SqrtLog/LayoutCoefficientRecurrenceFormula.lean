import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

namespace OAI.Algorithms

/-! Exact identification of the positive cache with the original coefficients. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

open scoped BigOperators
open SubexponentialSAT.BinomialInterpolation

theorem parity_zero (R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) 0 R j = (-2 : ℤ) ^ j.val := by
  rw [LayoutCoefficientBounds.parity_upper_recurrence]
  have hz : (∑ k : Fin R, if j.val < k.val then
      (Nat.choose 0 (k.val - j.val) : ℤ) * parityCoefficients (K := ℤ) 0 R k
      else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    split_ifs with h
    · simp [Nat.choose_eq_zero_of_lt (show 0 < k.val - j.val by omega)]
    · rfl
  rw [hz]
  simp

/-- The unsigned cache gives the exact original integer interpolation vector. -/
theorem parity_eq_H (A R : ℕ) (j : Fin R) :
    parityCoefficients (K := ℤ) A R j =
      (-1 : ℤ) ^ (A + j.val) * 2 ^ j.val * (H A (R - 1 - j.val) : ℤ) := by
  induction A generalizing j with
  | zero =>
    rw [parity_zero]
    simp only [H_zero, Nat.cast_one, mul_one, zero_add]
    rw [← mul_pow]
    norm_num
  | succ A ih =>
    cases R with
    | zero => exact Fin.elim0 j
    | succ n =>
      induction j using Fin.reverseInduction with
      | last =>
        have hs := parity_step A (n + 1) (Fin.last n)
        simp only [Fin.val_last, lt_self_iff_false, dite_false, add_zero] at hs
        rw [ih] at hs
        simp only [Fin.val_last, Nat.add_sub_cancel, Nat.sub_self, H_zero_right,
          Nat.cast_one, mul_one] at hs ⊢
        rw [show A + 1 + n = (A + n) + 1 by omega, pow_succ]
        linear_combination hs
      | cast j hj =>
        have hs := parity_step A (n + 1) j.castSucc
        simp only [Fin.val_castSucc] at hs
        rw [dite_eq_left (show j.val + 1 < n + 1 by omega)] at hs
        change parityCoefficients (K := ℤ) (A + 1) (n + 1) j.castSucc +
          parityCoefficients (K := ℤ) (A + 1) (n + 1) j.succ =
          -parityCoefficients (K := ℤ) A (n + 1) j.castSucc at hs
        rw [hj, ih] at hs
        simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_sub_cancel] at hs ⊢
        have hn : n - j.val = (n - (j.val + 1)) + 1 := by omega
        rw [hn, H_succ_succ]
        rw [← hn]
        push_cast
        rw [show A + 1 + j.val = (A + j.val) + 1 by omega, pow_succ]
        rw [show A + 1 + (j.val + 1) = (A + j.val) + 2 by omega,
          pow_add] at hs
        simp only [pow_succ] at hs
        norm_num at hs
        linear_combination hs

theorem natAbs_parity_eq_H (A R : ℕ) (j : Fin R) :
    (parityCoefficients (K := ℤ) A R j).natAbs =
      2 ^ j.val * H A (R - 1 - j.val) := by
  rw [parity_eq_H]
  simp [Int.natAbs_mul, Int.natAbs_pow]

/-- Every entry of the prefix cache has the existing uniform coefficient bound. -/
theorem H_le (A Q R m : ℕ) (hAQ : A ≤ Q) (hQ : 1 ≤ Q) (hm : m < R) :
    H A m ≤ (4 * Q) ^ R := by
  have h := LayoutCoefficientBounds.natAbs_parityCoefficients_le
    A (m + 1) Q hAQ hQ (0 : Fin (m + 1))
  rw [natAbs_parity_eq_H] at h
  simp only [Fin.val_zero, pow_zero, Nat.add_sub_cancel, Nat.sub_zero, one_mul] at h
  exact h.trans (Nat.pow_le_pow_right (by omega) (by omega))

end SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

end OAI.Algorithms
