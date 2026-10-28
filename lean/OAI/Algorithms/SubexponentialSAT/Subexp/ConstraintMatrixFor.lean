import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! A bounded contract for the existing fixed unary iterator. Only indices
that are actually visited require a callback trace; this supports finite
slot, color, and position cursors without a fictitious out-of-range call. -/

namespace SubexponentialSAT.Subexp.ConstraintMatrixFor

open BitProgram StructuredCalls UnaryForPrograms
open CounterForPrograms (budgetSum)

variable {R S : ℕ}

abbrev BodyStep (p : Ports R S) (body : Cmd R S) (bound : ℕ)
    (I : ℕ → State R S → Prop) (cost : ℕ → ℕ) : Prop :=
  ∀ i, i < bound → ∀ d, I i d → ∃ n e, n ≤ cost i ∧ Eval body n d e ∧
    e.stacks p.counter = d.stacks p.counter ∧ I (i + 1) e

theorem visits_exists (p : Ports R S) (body : Cmd R S) (bound : ℕ)
    (I : ℕ → State R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodyStep p body bound I cost) (word : List Bool) :
    ∀ i d, i + word.length ≤ bound → d.stacks p.counter = word → I i d →
      ∃ costs n e, Visits p body costs n d e ∧ I (i + word.length) e ∧
        costs.sum ≤ budgetSum cost i word.length := by
  induction word with
  | nil =>
      intro i d hbound hw hi
      have hp : I i (popped p d) := stable i d (popped p d)
        (fun j hj => (popped_other p d j hj).symm) hi
      exact ⟨[], 2, popped p d, .done d hw, by simpa using hp, by simp [budgetSum]⟩
  | cons bit word ih =>
      intro i d hbound hw hi
      have hp : I i (popped p d) := stable i d (popped p d)
        (fun j hj => (popped_other p d j hj).symm) hi
      have hib : i < bound := by
        simp only [List.length_cons] at hbound
        omega
      obtain ⟨nb, e, hn, he, hc, hei⟩ := spec i hib (popped p d) hp
      have hew : e.stacks p.counter = word := by simp only [hc, popped_counter, hw, List.tail_cons]
      have hnext : i + 1 + word.length ≤ bound := by
        simp only [List.length_cons] at hbound
        omega
      obtain ⟨costs, nt, f, ht, hfi, hcost⟩ := ih (i + 1) e hnext hew hei
      refine ⟨nb :: costs, nb + nt + 2, f,
        .step (by simp [hw]) he hc ht, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfi
      · simpa only [List.sum_cons, List.length_cons, budgetSum] using Nat.add_le_add hn hcost

theorem for_correct (p : Ports R S) (body : Cmd R S) (bound : ℕ)
    (I : ℕ → State R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodyStep p body bound I cost)
    (d : State R S) (hcount : (d.stacks p.counter).length = bound) (hi : I 0 d) :
    ∃ costs n e, Visits p body costs n d e ∧ Eval (forCmd p body) n d e ∧
      I bound e ∧ e.stacks p.counter = [] ∧ costs.length = bound ∧
      n = costs.sum + 2 * bound + 2 ∧ costs.sum ≤ budgetSum cost 0 bound := by
  obtain ⟨costs, n, e, hv, hei, hb⟩ := visits_exists p body bound I cost stable spec
    (d.stacks p.counter) 0 d (by omega) rfl hi
  rcases hv.bounds with ⟨hlen, hempty, hn⟩
  refine ⟨costs, n, e, hv, hv.eval, ?_, hempty, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add, hcount] using hei
  · exact hlen.trans hcount
  · simpa only [hlen, hcount] using hn
  · simpa only [hcount] using hb

theorem for_correct_constant (p : Ports R S) (body : Cmd R S) (bound C : ℕ)
    (I : ℕ → State R S → Prop) (stable : FrameStable p I)
    (spec : BodyStep p body bound I (fun _ => C))
    (d : State R S) (hcount : (d.stacks p.counter).length = bound) (hi : I 0 d) :
    ∃ n ≤ bound * (C + 2) + 2, ∃ e,
      Eval (forCmd p body) n d e ∧ I bound e ∧ e.stacks p.counter = [] := by
  obtain ⟨costs, n, e, _, he, hei, hempty, _, hn, hb⟩ :=
    for_correct p body bound I (fun _ => C) stable spec d hcount hi
  rw [CounterForPrograms.budgetSum_const] at hb
  refine ⟨n, ?_, e, he, hei, hempty⟩
  nlinarith only [hn, hb]

end SubexponentialSAT.Subexp.ConstraintMatrixFor

end OAI.Algorithms
