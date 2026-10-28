import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchCompanion

namespace OAI.Algorithms

/-! A sequential list implementation of one companion-matrix step. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearch

variable {R : Type*} [Ring R]

def companionScan (tail previous : R) : List (R × R) → List R
  | [] => []
  | (c, a) :: xs => (previous - tail * c) :: companionScan tail a xs

theorem companionScan_ofFn {d : ℕ} (tail previous : R) (c a : Fin d → R) :
    companionScan tail previous (List.ofFn (fun i => (c i, a i))) =
      List.ofFn (fun i => (if _h : i.val = 0 then previous
        else a ⟨i.val - 1, by omega⟩) - tail * c i) := by
  induction d generalizing previous with
  | zero => simp [companionScan]
  | succ d ih =>
      rw [List.ofFn_succ, companionScan, List.ofFn_succ]
      congr 1
      rw [ih]
      apply congrArg List.ofFn
      funext i
      simp only [Fin.val_succ, Nat.add_sub_cancel, Nat.add_eq_zero_iff,
        one_ne_zero, and_false, dite_false]
      split_ifs with hi
      · congr 1
        congr 1
        apply Fin.ext
        simp [hi]
      · congr 1
        congr 1
        apply Fin.ext
        simp only [Fin.val_succ]
        omega

theorem companionScan_eq_mulX {d : ℕ} (c a : Fin d → R) :
    companionScan (entry a (d - 1)) 0 (List.ofFn (fun i => (c i, a i))) =
      List.ofFn (mulX c a) := by
  rw [companionScan_ofFn]
  apply congrArg List.ofFn
  funext i
  unfold mulX
  by_cases hi : i.val = 0
  · simp [hi]
  · simp [hi, entry, show i.val - 1 < d by omega]

end SubexponentialSAT.SqrtLog.IrreducibleSearch

end OAI.Algorithms
