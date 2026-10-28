import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashInput

namespace OAI.Algorithms

/-! Weighted selector mass is the sum of ordinary marked-clause counts.
This identity justifies executing the same count pipeline once per supplied
clause; no weighted arithmetic is hidden in the local indicator evaluator. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram

open scoped BigOperators

variable {X Row E : Type*} [Fintype X] [Fintype E]

def markedCount (rowAccept : Row → X → Bool) (rows : List Row)
    (bad : E → X → Bool) (e : E) : ℕ :=
  ∑ x, if HashSelect.accepts rowAccept rows x && bad e x then 1 else 0

def violationWeight (bad : E → X → Bool) (x : X) : ℕ :=
  ∑ e, if bad e x then 1 else 0

theorem sum_markedCount (rowAccept : Row → X → Bool) (rows : List Row)
    (bad : E → X → Bool) :
    (∑ e, markedCount rowAccept rows bad e) =
      HashSelect.mass rowAccept (violationWeight bad) rows := by
  unfold markedCount HashSelect.mass violationWeight
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  cases h : HashSelect.accepts rowAccept rows x <;> simp []

omit [Fintype E] in
theorem markedCount_le (rowAccept : Row → X → Bool) (rows : List Row)
    (bad : E → X → Bool) (e : E) :
    markedCount rowAccept rows bad e ≤ Fintype.card X := by
  calc
    _ ≤ ∑ _x : X, 1 := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
    _ = _ := by simp

variable {V : Type*} [Fintype V] [DecidableEq V] [DecidableEq E]

omit [Fintype V] [DecidableEq V] [DecidableEq E] in
theorem cnf_weight (C : E → SAT.Clause V) (x : SAT.Assignment V) :
    violationWeight (fun e x => !(C e).eval x) x = HashInput.violationWeight C x := by
  unfold violationWeight HashInput.violationWeight
  apply Finset.sum_congr rfl
  intro e _
  cases h : (C e).eval x <;> simp [h]

omit [DecidableEq E] in
theorem sum_marked_cnf (rowAccept : Row → SAT.Assignment V → Bool) (rows : List Row)
    (C : E → SAT.Clause V) :
    (∑ e, markedCount rowAccept rows (fun e x => !(C e).eval x) e) =
      HashSelect.mass rowAccept (HashInput.violationWeight C) rows := by
  rw [sum_markedCount]
  congr 1
  funext x
  exact cnf_weight C x

end SubexponentialSAT.SqrtLog.LeafProgram

end OAI.Algorithms
