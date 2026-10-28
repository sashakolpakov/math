import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafParametersProgram

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafParametersProgram

theorem size_eq_log2_add_one {n : ℕ} (hn : n ≠ 0) : Nat.size n = Nat.log2 n + 1 := by
  have hu : Nat.size n ≤ Nat.log2 n + 1 :=
    Nat.size_le.mpr ((Nat.log2_lt hn).mp (by omega))
  have hl : Nat.log2 n < Nat.size n :=
    Nat.lt_size.mpr ((Nat.le_log2 hn).mp le_rfl)
  omega

theorem two_pow_size_le (n : ℕ) : 2 ^ Nat.size n ≤ 2 * (n + 1) := by
  by_cases hn : n = 0
  · subst n; norm_num
  · rw [size_eq_log2_add_one hn, pow_succ]
    have h : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn).mp le_rfl
    omega

theorem extensionDegree_card_bound (Q : ℕ) :
    3 ^ extensionDegree Q ≤ 16 * (Q + 1) ^ 2 := by
  have h : 2 ^ extensionDegree Q ≤ 4 * (Q + 1) := by
    rw [extensionDegree, pow_succ]
    have := two_pow_size_le Q
    omega
  calc
    3 ^ extensionDegree Q ≤ 4 ^ extensionDegree Q := Nat.pow_le_pow_left (by decide) _
    _ = (2 ^ extensionDegree Q) ^ 2 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ (4 * (Q + 1)) ^ 2 := Nat.pow_le_pow_left h _
    _ = 16 * (Q + 1) ^ 2 := by ring

def fieldCard (x : Input) : ℕ := 3 ^ (produce x).d

def inverseExponent (x : Input) : ℕ := fieldCard x - 2

theorem fieldCard_le (x : Input) : fieldCard x ≤ 16 * ((produce x).Q + 1) ^ 2 :=
  extensionDegree_card_bound _

theorem inverseExponent_le (x : Input) :
    inverseExponent x ≤ 16 * ((produce x).Q + 1) ^ 2 :=
  (Nat.sub_le _ _).trans (fieldCard_le x)

theorem precision_le (n m : ℕ) : precision n m ≤ n + m + 1 := by
  have hs : Nat.size m ≤ m := by
    apply Nat.size_le.mpr
    exact Nat.lt_two_pow_self
  unfold precision
  omega

end SubexponentialSAT.SqrtLog.LeafParametersProgram

end OAI.Algorithms
