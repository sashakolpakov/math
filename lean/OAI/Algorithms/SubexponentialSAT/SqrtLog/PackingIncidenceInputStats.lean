import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PackingIncidenceInputSemantics
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsProgramSpec

namespace OAI.Algorithms

/-! The address stream and the native statistics use the same mask scan. -/
namespace SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats
open SubexponentialSAT.Subexp
open LeafStatisticsProgram

theorem factors_length (scopes : List (List ℕ)) (v z : ℕ) :
    (Step.factors scopes v z).length = max 1 (degree scopes v) := by
  change (Step.factors scopes v z).length = max 1 (Scan.indices scopes v).length
  cases h : Scan.indices scopes v with
  | nil => simp [Step.factors,h]
  | cons e es => simp [Step.factors,h]

theorem next_eq (scopes : List (List ℕ)) (v z : ℕ) :
    Step.next scopes v z = z + if degree scopes v = 0 then 1 else 0 := by
  change Step.next scopes v z = z + if (Scan.indices scopes v).length = 0 then 1 else 0
  by_cases h : Scan.indices scopes v = [] <;>
    simp [Step.next,List.length_eq_zero_iff,h]

theorem counter_agrees (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z (t : Totals), Loop.finalCounter scopes v z mask + t.uncovered =
      z + (variableTotals scopes v mask t).uncovered := by
  induction mask with
  | nil => intros; simp [Loop.finalCounter,variableTotals]
  | cons b bs ih =>
      intro v z t
      cases b
      · have h := ih (v+1) (Step.next scopes v z) (t.add (degree scopes v))
        simp only [Totals.add,next_eq] at h
        simp only [Loop.finalCounter,variableTotals,Bool.false_eq_true,ite_false]
        simp only [Totals.add,next_eq] at *
        omega
      · simpa [Loop.finalCounter,variableTotals] using ih (v+1) z t

theorem entries_agree (scopes : List (List ℕ)) (mask : List Bool) :
    ∀ v z (t : Totals), (Semantics.entries scopes v z mask).length + t.incidences =
      (variableTotals scopes v mask t).incidences := by
  induction mask with
  | nil => intros; simp [Semantics.entries,variableTotals]
  | cons b bs ih =>
      intro v z t
      cases b
      · have h := ih (v+1) (Step.next scopes v z) (t.add (degree scopes v))
        simp only [Totals.add] at h
        simp only [Semantics.entries,variableTotals,Bool.false_eq_true,ite_false,
          List.length_append,List.length_map,factors_length]
        simp only [Totals.add] at *
        omega
      · simpa [Semantics.entries,variableTotals] using ih (v+1) z t

def zero : Totals := ⟨0,0,0,0⟩
theorem native_factor_count (scopes : List (List ℕ)) (mask : List Bool) :
    Semantics.factorCount scopes mask = scopes.length +
      (variableTotals scopes 0 mask zero).uncovered := by
  simpa [Semantics.factorCount,zero] using counter_agrees scopes mask 0 scopes.length zero
theorem native_incidence_count (scopes : List (List ℕ)) (n : ℕ) (mask : List Bool) :
    (Loop.plans scopes n 0 scopes.length mask).length =
      (variableTotals scopes 0 mask zero).incidences := by
  rw [Semantics.plans_eq,List.length_map]
  simpa [zero] using entries_agree scopes mask 0 scopes.length zero
end SubexponentialSAT.SqrtLog.PackingIncidenceInput.Stats

end OAI.Algorithms
