import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! A measured unary loop whose body contract is needed only before the
supplied terminal index. The final empty-counter state never invokes it. -/

namespace SubexponentialSAT.SubexpLagrangeBoundedLoop

open BitProgram StructuredCalls UnaryForPrograms
open CounterForPrograms (budgetSum)

variable {R S : ℕ}

theorem visits_exists (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop) (cost : ℕ → ℕ) (limit : ℕ)
    (stable : FrameStable p I)
    (spec : ∀ i, i < limit → ∀ d, I i d →
      ∃ n e, n ≤ cost i ∧ Eval body n d e ∧
        e.stacks p.counter = d.stacks p.counter ∧ I (i + 1) e)
    (word : List Bool) :
    ∀ i d, i + word.length ≤ limit → d.stacks p.counter = word → I i d →
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
      obtain ⟨nb, e, hn, he, hc, hei⟩ := spec i (by
        simp only [List.length_cons] at hbound
        omega) (popped p d) hp
      have hew : e.stacks p.counter = word := by
        simp only [hc, popped_counter, hw, List.tail_cons]
      obtain ⟨costs, nt, f, ht, hfi, hcost⟩ := ih (i + 1) e
        (by simp only [List.length_cons] at hbound; omega) hew hei
      refine ⟨nb :: costs, nb + nt + 2, f,
        .step (by simp [hw]) he hc ht, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfi
      · simpa only [List.sum_cons, List.length_cons, budgetSum] using Nat.add_le_add hn hcost

theorem for_correct (p : Ports R S) (body : Cmd R S)
    (I : ℕ → State R S → Prop) (cost : ℕ → ℕ) (limit : ℕ)
    (stable : FrameStable p I)
    (spec : ∀ i, i < limit → ∀ d, I i d →
      ∃ n e, n ≤ cost i ∧ Eval body n d e ∧
        e.stacks p.counter = d.stacks p.counter ∧ I (i + 1) e)
    (d : State R S) (hlimit : (d.stacks p.counter).length = limit) (hi : I 0 d) :
    ∃ n e, Eval (forCmd p body) n d e ∧ I limit e ∧ e.stacks p.counter = [] ∧
      n ≤ budgetSum cost 0 limit + 2 * limit + 2 := by
  obtain ⟨costs, n, e, hv, hei, hc⟩ := visits_exists p body I cost limit stable spec
    (d.stacks p.counter) 0 d (by simp [hlimit]) rfl hi
  obtain ⟨hlen, hempty, htime⟩ := hv.bounds
  refine ⟨n, e, hv.eval, ?_, hempty, ?_⟩
  · simpa [hlimit] using hei
  · rw [hlimit] at hlen hc
    rw [htime, hlen]
    omega

end SubexponentialSAT.SubexpLagrangeBoundedLoop

end OAI.Algorithms
