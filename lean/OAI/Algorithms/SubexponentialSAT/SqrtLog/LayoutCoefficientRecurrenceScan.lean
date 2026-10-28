import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

namespace OAI.Algorithms

/-! A left-to-right add/shift scan constructs each unsigned cache row. -/

namespace SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

def scanDouble (prior : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs =>
    let y := 2 * prior + x
    y :: scanDouble y xs

@[simp] theorem scanDouble_length (prior : ℕ) (xs : List ℕ) :
    (scanDouble prior xs).length = xs.length := by
  induction xs generalizing prior with
  | nil => rfl
  | cons x xs ih => simp only [scanDouble, List.length_cons, ih]

def scanPrior (A : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => H (A + 1) n

theorem scan_cell (A n : ℕ) :
    2 * scanPrior A n + H A n = H (A + 1) n := by
  cases n with
  | zero => simp [scanPrior]
  | succ n => simp [scanPrior, H_succ_succ, Nat.add_comm]

theorem scanDouble_H_offset (A R n : ℕ) :
    scanDouble (scanPrior A n) ((List.range R).map (fun m => H A (n + m))) =
      (List.range R).map (fun m => H (A + 1) (n + m)) := by
  induction R generalizing n with
  | zero => rfl
  | succ R ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero,
      scanDouble, scan_cell]
    congr 1
    have hfun : (fun m => H A (n + m)) ∘ Nat.succ =
        fun m => H A ((n + 1) + m) := by
      funext m
      simp only [Function.comp_apply]
      congr 1
      omega
    have hfun' : (fun m => H (A + 1) (n + m)) ∘ Nat.succ =
        fun m => H (A + 1) ((n + 1) + m) := by
      funext m
      simp only [Function.comp_apply]
      congr 1
      omega
    rw [hfun, hfun']
    simpa only [scanPrior] using ih (n + 1)

theorem scanDouble_H (A R : ℕ) :
    scanDouble 0 ((List.range R).map (H A)) =
      (List.range R).map (H (A + 1)) := by
  simpa only [scanPrior, Nat.zero_add] using scanDouble_H_offset A R 0

end SubexponentialSAT.SqrtLog.LayoutCoefficientRecurrence

end OAI.Algorithms
