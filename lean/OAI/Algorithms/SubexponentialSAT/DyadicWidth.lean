import OAI.Algorithms.SubexponentialSAT.LeanCompat

namespace OAI.Algorithms

/-! A positive dyadic width for bounded tuple enumeration, including zero. -/

namespace SubexponentialSAT.DyadicWidth

def width (m : ℕ) : ℕ := Nat.log 2 m + 1

theorem width_pos (m : ℕ) : 0 < width m := by
  unfold width
  omega

theorem lt_two_pow_width (m : ℕ) : m < 2 ^ width m :=
  Nat.lt_pow_succ_log_self (by decide) m

theorem two_pow_width_le (m : ℕ) : 2 ^ width m ≤ 2 * (m + 1) := by
  by_cases hm : m = 0
  · subst m
    norm_num [width]
  · have h := Nat.pow_log_le_self 2 hm
    unfold width
    rw [pow_succ]
    omega

theorem width_le_succ (m : ℕ) : width m ≤ m + 1 := by
  by_cases hm : m = 0
  · subst m
    norm_num [width]
  · have h := Nat.log_lt_self 2 hm
    unfold width
    omega

theorem tuple_count_le (m r : ℕ) :
    2 ^ (width m * r) ≤ (2 * (m + 1)) ^ r := by
  rw [pow_mul]
  exact Nat.pow_le_pow_left (two_pow_width_le m) r

end SubexponentialSAT.DyadicWidth

end OAI.Algorithms
