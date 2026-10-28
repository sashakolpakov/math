import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

namespace OAI.Algorithms

/-! Bounds for unsigned component totals in a signed-pair implementation.
Cancellation is not needed for this triangular bound. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

open scoped BigOperators
open SubexponentialSAT.SqrtLog.LayoutCoefficientBounds

theorem upper_magnitude_bound (A R Q : ℕ) (hAQ : A ≤ Q) (hQ : 1 ≤ Q)
    (m : Fin R → ℕ)
    (hm : ∀ i, m i ≤ 2 ^ i.val + ∑ k : Fin R,
      if i.val < k.val then A.choose (k.val - i.val) * m k else 0)
    (j : Fin R) : m j ≤ (4 * Q) ^ R := by
  let b : Fin R → ℕ := fun k => Q ^ k.val * m k
  let M := Q ^ R * 2 ^ R
  have hb : ∀ i, b i ≤ M + ∑ k : Fin R, if i.val < k.val then b k else 0 := by
    intro i
    calc
      b i ≤ Q ^ i.val * (2 ^ i.val + ∑ k : Fin R, if i.val < k.val then
          A.choose (k.val - i.val) * m k else 0) := Nat.mul_le_mul_left _ (hm i)
      _ = Q ^ i.val * 2 ^ i.val + ∑ k : Fin R, if i.val < k.val then
          Q ^ i.val * (A.choose (k.val - i.val) * m k) else 0 := by
        rw [Nat.mul_add, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro k hk
        split_ifs <;> simp
      _ ≤ M + ∑ k : Fin R, if i.val < k.val then b k else 0 := by
        apply Nat.add_le_add
        · exact Nat.mul_le_mul (Nat.pow_le_pow_right hQ (Nat.le_of_lt i.isLt))
            (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt i.isLt))
        · apply Finset.sum_le_sum
          intro k hk
          split_ifs with hik
          · have hc : A.choose (k.val - i.val) ≤ Q ^ (k.val - i.val) :=
              (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hAQ _)
            calc
              _ ≤ Q ^ i.val * (Q ^ (k.val - i.val) * m k) :=
                Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hc)
              _ = b k := by
                rw [← Nat.mul_assoc, ← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hik)]
          · exact Nat.le_refl _
  have hs := triangular_sum_bound R M b hb
  have hj : b j ≤ ∑ i, b i :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hsmall : m j ≤ b j := by
    dsimp [b]
    have hp : 1 ≤ Q ^ j.val := one_le_pow₀ hQ
    simpa using Nat.mul_le_mul_right (m j) hp
  calc
    _ ≤ M * 2 ^ R := hsmall.trans (hj.trans (le_trans (Nat.le_add_right _ _) hs))
    _ = (4 * Q) ^ R := by
      dsimp [M]
      rw [mul_pow, show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]
      ring

end SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm

end OAI.Algorithms
