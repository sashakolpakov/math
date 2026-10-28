import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionEnumeration

namespace OAI.Algorithms

/-! Exact candidate counts for the ordered-tuple implementation. These are
operation counts, not a primitive bit-machine time theorem. -/

namespace SubexponentialSAT.SqrtLog.RowSelection

open scoped BigOperators

theorem candidates_length (a b K : ℕ) :
    (candidates a b K).length = ((List.range (K+1)).map fun s => a^s*b^s).sum := by
  simp [candidates, List.length_flatMap ]

theorem candidates_length_le (a b K : ℕ) :
    (candidates a b K).length ≤ (K+1) * (a*b+1)^K := by
  rw [candidates_length]
  calc
    _ ≤ ((List.range (K+1)).map fun _ => (a*b+1)^K).sum := by
      apply List.sum_le_sum
      intro s hs
      have hsK : s ≤ K := Nat.le_of_lt_succ (List.mem_range.mp hs)
      rw [← mul_pow]
      exact (Nat.pow_le_pow_left (Nat.le_succ _) s).trans
        (Nat.pow_le_pow_right (by omega) hsK)
    _ = (K+1) * (a*b+1)^K := by simp

/-- Each scanned candidate performs one exact nonzero determinant test. -/
def scanCalls {a b : ℕ} : List (Candidate a b) → ℕ
  | [] => 0
  | _ :: rest => scanCalls rest + 1

@[simp] theorem scanCalls_eq_length {a b : ℕ} (cs : List (Candidate a b)) :
    scanCalls cs = cs.length := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [scanCalls, ih]

theorem selectCalls_le (a b cap : ℕ) :
    scanCalls (candidates a b (limit a b cap)) ≤
      (cap+1) * (a*b+1)^cap := by
  rw [scanCalls_eq_length]
  have hK : limit a b cap ≤ cap := min_le_left _ _
  exact (candidates_length_le a b _).trans
    (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by omega) hK))

end SubexponentialSAT.SqrtLog.RowSelection

end OAI.Algorithms
