import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramSpec

namespace OAI.Algorithms

/-! Closed finite-sum and maximum specifications of the native variable scan. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram

def scanSum (f : ℕ → ℕ) (v : ℕ) (mask : List Bool) : ℕ :=
  ∑ i : Fin mask.length, if mask.get i then 0 else f (v + i.val)

@[simp] theorem scanSum_nil (f : ℕ → ℕ) (v : ℕ) : scanSum f v [] = 0 := by
  simp [scanSum]

@[simp] theorem scanSum_cons (f : ℕ → ℕ) (v : ℕ) (b : Bool) (bs : List Bool) :
    scanSum f v (b :: bs) = (if b then 0 else f v) + scanSum f (v+1) bs := by
  simp [scanSum, Fin.sum_univ_succ, Nat.add_comm, Nat.add_left_comm]

theorem totals_free (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).free = t.free + scanSum (fun _ => 1) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

theorem totals_incidences (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).incidences =
      t.incidences + scanSum (fun i => max 1 (degree scopes i)) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

theorem totals_uncovered (scopes : List (List ℕ)) (v : ℕ) (mask : List Bool) (t : Totals) :
    (variableTotals scopes v mask t).uncovered =
      t.uncovered + scanSum (fun i => if degree scopes i = 0 then 1 else 0) v mask := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    cases b <;> simp [variableTotals, Totals.add, ih, Nat.add_assoc]

theorem totals_occurrence_le_iff (scopes : List (List ℕ)) (v : ℕ)
    (mask : List Bool) (t : Totals) (B : ℕ) :
    (variableTotals scopes v mask t).occurrence ≤ B ↔
      t.occurrence ≤ B ∧
        ∀ i : Fin mask.length, mask.get i = false → max 1 (degree scopes (v+i.val)) ≤ B := by
  induction mask generalizing v t with
  | nil => simp [variableTotals]
  | cons b bs ih =>
    rw [variableTotals, ih]
    cases b <;>
      simp [Totals.add, Fin.forall_fin_succ,
        Nat.add_comm, Nat.add_left_comm, and_assoc, and_left_comm, and_comm]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
