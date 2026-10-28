import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.HashSelectGreedy

namespace OAI.Algorithms

/-! Bounds on every evaluated matrix and on the sum of all evaluation
costs, rather than only on the selected final matrix. -/

namespace SubexponentialSAT.SqrtLog.HashSelect

variable {R : Type*} {c : ℕ}

theorem mem_allTrials (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (initial : List R) (K : ℕ) (q : List R)
    (hq : q ∈ allTrials evaluate family initial K) :
    ∃ t < K, q ∈ trials evaluate family (run evaluate family initial t) := by
  induction K with
  | zero => simp [allTrials] at hq
  | succ K ih =>
    rcases List.mem_append.mp hq with h | h
    · obtain ⟨t, ht, hq⟩ := ih h
      exact ⟨t, by omega, hq⟩
    · exact ⟨K, by omega, h⟩

theorem allTrials_bounds (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (initial : List R) (cost : R → ℕ) (d K : ℕ)
    (hcost : ∀ i, cost (family i) ≤ d) (q : List R)
    (hq : q ∈ allTrials evaluate family initial K) :
    q.length ≤ initial.length + K ∧
      totalCost cost q ≤ totalCost cost initial + K * d := by
  obtain ⟨t, ht, hq⟩ := mem_allTrials evaluate family initial K q hq
  obtain ⟨hl, hc⟩ := trial_bounds evaluate family initial cost d t hcost q hq
  constructor
  · omega
  · exact hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_right d (by omega : t + 1 ≤ K)) _)

theorem trials_property (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (rows : List R) (P : R → Prop) (hrows : ∀ r ∈ rows, P r)
    (hfamily : ∀ i, P (family i)) (q : List R)
    (hq : q ∈ trials evaluate family rows) : ∀ r ∈ q, P r := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
  have hp := pickTrace_property (fun r => evaluate (r :: rows)) family P hfamily a ha
  intro r hr
  rcases List.mem_cons.mp hr with h | h
  · simpa [h] using hp
  · exact hrows r h

theorem allTrials_property (evaluate : List R → ℕ) (family : Fin (c + 1) → R)
    (initial : List R) (P : R → Prop) (hinit : ∀ r ∈ initial, P r)
    (hfamily : ∀ i, P (family i)) (K : ℕ) (q : List R)
    (hq : q ∈ allTrials evaluate family initial K) : ∀ r ∈ q, P r := by
  obtain ⟨t, _, hq⟩ := mem_allTrials evaluate family initial K q hq
  exact trials_property evaluate family _ P
    (run_property evaluate family initial P hinit hfamily t) hfamily q hq

private theorem map_sum_le {A : Type*} (f : A → ℕ) (xs : List A) (T : ℕ)
    (h : ∀ x ∈ xs, f x ≤ T) : (xs.map f).sum ≤ xs.length * T := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have hi := ih (fun x hx => h x (by simp [hx]))
    simpa [Nat.add_mul, Nat.add_comm] using Nat.add_le_add ha hi

theorem total_evaluator_cost (evaluate : List R → ℕ)
    (family : Fin (c + 1) → R) (initial : List R) (K T : ℕ)
    (queryCost : List R → ℕ)
    (hcost : ∀ q ∈ allTrials evaluate family initial K, queryCost q ≤ T) :
    ((allTrials evaluate family initial K).map queryCost).sum ≤
      (2 * (c + 1) * K) * T := by
  simpa only [allTrials_length] using
    map_sum_le queryCost (allTrials evaluate family initial K) T hcost

end SubexponentialSAT.SqrtLog.HashSelect

end OAI.Algorithms
