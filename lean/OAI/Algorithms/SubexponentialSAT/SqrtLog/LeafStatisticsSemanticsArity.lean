import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

open scoped BigOperators
open LeafStatisticsProgram HighIncidence

theorem low_iff (mask : List Bool) (i : ℕ) :
    Scope.low mask i = true ↔ ∃ hi : i < mask.length, mask.get ⟨i, hi⟩ = false := by
  by_cases hi : i < mask.length
  · simp [Scope.low, hi]
  · simp [Scope.low, hi]

theorem residual_mem (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length) (v : Free mask) :
    v ∈ residualScope scopes mask e ↔ v.val.val ∈ scopes.get e := by
  simp [residualScope, remainingScope]

theorem residual_card (scopes : List (List ℕ)) (mask : List Bool)
    (e : Fin scopes.length) (hn : (scopes.get e).Nodup) :
    (residualScope scopes mask e).card = ((scopes.get e).filter (Scope.low mask)).length := by
  rw [← List.toFinset_card_of_nodup (hn.filter _)]
  apply Finset.card_bij (fun v _ => v.val.val)
  · intro v hv
    apply List.mem_toFinset.mpr
    apply List.mem_filter.mpr
    exact ⟨(residual_mem scopes mask e v).mp hv,
      (low_iff mask v.val.val).mpr ⟨v.val.isLt, free_bit mask v⟩⟩
  · intro v hv w hw h
    apply Subtype.ext
    exact Fin.ext h
  · intro i hi
    obtain ⟨hirow, hilow⟩ := List.mem_filter.mp (List.mem_toFinset.mp hi)
    obtain ⟨hib, hibit⟩ := (low_iff mask i).mp hilow
    simp only [List.get_eq_getElem] at hibit
    let v : Free mask := ⟨⟨i, hib⟩, by simp [hibit]⟩
    exact ⟨v, (residual_mem scopes mask e v).mpr hirow, rfl⟩

theorem arity_le_iff (mask : List Bool) (scopes : List (List ℕ)) (a b : ℕ) :
    Arity.arity mask scopes a ≤ b ↔
      a ≤ b ∧ ∀ row ∈ scopes, (row.filter (Scope.low mask)).length ≤ b := by
  induction scopes generalizing a with
  | nil => simp [Arity.arity]
  | cons row rows ih =>
    change Arity.arity mask rows (max (row.filter (Scope.low mask)).length a) ≤ b ↔ _
    rw [ih]
    simp [ and_assoc, and_comm]

theorem raw_arity_exact (mask : List Bool) (scopes : List (List ℕ))
    (hn : ∀ row ∈ scopes, row.Nodup) :
    Arity.arity mask scopes 0 = Finset.univ.sup (fun e => (residualScope scopes mask e).card) := by
  apply Nat.le_antisymm
  · rw [arity_le_iff]
    refine ⟨Nat.zero_le _, ?_⟩
    intro row hrow
    obtain ⟨e, rfl⟩ := List.get_of_mem hrow
    rw [← residual_card scopes mask e (hn _ (List.get_mem _ _))]
    exact Finset.le_sup (f := fun e => (residualScope scopes mask e).card)
      (Finset.mem_univ e)
  · apply Finset.sup_le
    intro e _
    rw [residual_card scopes mask e (hn _ (List.get_mem _ _))]
    exact ((arity_le_iff mask scopes 0 (Arity.arity mask scopes 0)).mp le_rfl).2
      _ (List.get_mem _ _)

theorem completed_arity_exact (mask : List Bool) (scopes : List (List ℕ))
    (hn : ∀ row ∈ scopes, row.Nodup) :
    max (Arity.arity mask scopes 0)
      (if (variableTotals scopes 0 mask zero).uncovered = 0 then 0 else 1) =
        Finset.univ.sup (fun e => (completedScope scopes mask e).card) := by
  rw [raw_arity_exact mask scopes hn, uncovered_exact, completedScope, neutral_arity_eq]
  congr 1
  by_cases h : (uncovered (residualScope scopes mask)).Nonempty
  · have hc : (uncovered (residualScope scopes mask)).card ≠ 0 :=
      Nat.ne_of_gt (Finset.card_pos.mpr h)
    simp [h, hc]
  · have hc : (uncovered (residualScope scopes mask)).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    simp [h, hc]

end SubexponentialSAT.SqrtLog.LeafStatisticsSemantics

end OAI.Algorithms
