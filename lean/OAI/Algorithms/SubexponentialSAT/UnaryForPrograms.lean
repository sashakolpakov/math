import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterForPrograms

namespace OAI.Algorithms

/-!
# Fixed-control unary-counted callbacks

The counter is a Boolean stack whose length is the iteration count. Its bits
are ignored. The controller pops before each callback and tests the presence
flag; callbacks preserve the remaining counter tail and may clobber all
registers. Every observation contains an actual callback evaluation.
-/

namespace SubexponentialSAT.UnaryForPrograms

open BitProgram StructuredProgram
open CounterForPrograms (budgetSum)

abbrev Data := StructuredProgram.State

structure Ports (R S : ℕ) where
  counter : Fin S
  bit : Fin R
  flag : Fin R

variable {R S : ℕ}

abbrev popCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .base (.atom (.pop p.counter p.bit p.flag))

def popped (p : Ports R S) (d : Data R S) : Data R S :=
  ⟨readRegs d.regs p.bit p.flag (d.stacks p.counter).head?,
    Function.update d.stacks p.counter (d.stacks p.counter).tail⟩

theorem pop_eval (p : Ports R S) (d : Data R S) :
    StructuredCalls.Eval (popCmd p) 1 d (popped p d) := .base (.atom _ _)

@[simp] theorem popped_counter (p : Ports R S) (d : Data R S) :
    (popped p d).stacks p.counter = (d.stacks p.counter).tail := by simp [popped]

@[simp] theorem popped_flag (p : Ports R S) (d : Data R S) :
    (popped p d).regs p.flag = (d.stacks p.counter).head?.isSome := by
  simp [popped, readRegs]

theorem popped_other (p : Ports R S) (d : Data R S) (j : Fin S) (hj : j ≠ p.counter) :
    (popped p d).stacks j = d.stacks j := by simp [popped, hj]

abbrev loopCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .while p.flag (.seq body (popCmd p))

abbrev forCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .seq (popCmd p) (loopCmd p body)

def FrameStable (p : Ports R S) (I : ℕ → Data R S → Prop) : Prop :=
  ∀ i a b, (∀ j, j ≠ p.counter → a.stacks j = b.stacks j) → I i a → I i b

abbrev BodySpec (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ) : Prop :=
  ∀ i d, I i d → ∃ n e, n ≤ cost i ∧ StructuredCalls.Eval body n d e ∧
    e.stacks p.counter = d.stacks p.counter ∧ I (i + 1) e

inductive Visits (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    List ℕ → ℕ → Data R S → Data R S → Prop
  | done (d : Data R S) (hempty : d.stacks p.counter = []) :
      Visits p body [] 2 d (popped p d)
  | step {d e f : Data R S} {nb nt : ℕ} {costs : List ℕ}
      (hne : d.stacks p.counter ≠ [])
      (hbody : StructuredCalls.Eval body nb (popped p d) e)
      (hcounter : e.stacks p.counter = (popped p d).stacks p.counter)
      (tail : Visits p body costs nt e f) :
      Visits p body (nb :: costs) (nb + nt + 2) d f

theorem Visits.loop_eval {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    ∃ m, n = 1 + m ∧ StructuredCalls.Eval (loopCmd p body) m (popped p d) e := by
  induction h with
  | done d he =>
      exact ⟨1, rfl, .while_false (by simp [he])⟩
  | @step d e f nb nt costs hne hb hc ht ih =>
      obtain ⟨m, hm, he⟩ := ih
      have hf : (popped p d).regs p.flag = true := by
        rw [popped_flag]
        cases hw : d.stacks p.counter with
        | nil => exact False.elim (hne hw)
        | cons b bs => rfl
      refine ⟨(nb + 1) + m + 1, by omega, ?_⟩
      exact .while_true hf (hb.seq (pop_eval p e)) he

theorem Visits.eval {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    StructuredCalls.Eval (forCmd p body) n d e := by
  obtain ⟨m, hm, he⟩ := h.loop_eval
  rw [hm]
  exact (pop_eval p d).seq he

/-- Exact callback count and exact controller overhead, including the final
empty pop and false guard. -/
theorem Visits.bounds {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    costs.length = (d.stacks p.counter).length ∧ e.stacks p.counter = [] ∧
      n = costs.sum + 2 * costs.length + 2 := by
  induction h with
  | done d he => simp [he]
  | @step d e f nb nt costs hne hb hc ht ih =>
      rcases ih with ⟨hlen, hempty, htime⟩
      have hw : (e.stacks p.counter).length + 1 = (d.stacks p.counter).length := by
        rw [hc, popped_counter]
        cases hword : d.stacks p.counter with
        | nil => exact False.elim (hne hword)
        | cons b bs => simp
      refine ⟨?_, hempty, ?_⟩
      · simp only [List.length_cons, hlen]
        exact hw
      · simp only [List.sum_cons, List.length_cons]
        omega

theorem visits_exists (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost) (word : List Bool) :
    ∀ i d, d.stacks p.counter = word → I i d →
      ∃ costs n e, Visits p body costs n d e ∧ I (i + word.length) e ∧
        costs.sum ≤ budgetSum cost i word.length := by
  induction word with
  | nil =>
      intro i d hw hi
      have hp : I i (popped p d) := stable i d (popped p d)
        (fun j hj => (popped_other p d j hj).symm) hi
      exact ⟨[], 2, popped p d, .done d hw, by simpa using hp, by simp [budgetSum]⟩
  | cons bit word ih =>
      intro i d hw hi
      have hp : I i (popped p d) := stable i d (popped p d)
        (fun j hj => (popped_other p d j hj).symm) hi
      obtain ⟨nb, e, hn, he, hc, hei⟩ := spec i (popped p d) hp
      have hew : e.stacks p.counter = word := by simp only [hc, popped_counter, hw, List.tail_cons]
      obtain ⟨costs, nt, f, ht, hfi, hcost⟩ := ih (i + 1) e hew hei
      refine ⟨nb :: costs, nb + nt + 2, f,
        .step (by simp [hw]) he hc ht, ?_, ?_⟩
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfi
      · simpa only [List.sum_cons, List.length_cons, budgetSum] using Nat.add_le_add hn hcost

/-- Explicit observations of the actual callbacks, with a sum of their costs. -/
theorem for_correct_measured (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hi : I 0 d) :
    ∃ costs n e, Visits p body costs n d e ∧
      StructuredCalls.Eval (forCmd p body) n d e ∧
      costs.length = (d.stacks p.counter).length ∧
      I (d.stacks p.counter).length e ∧ e.stacks p.counter = [] ∧
      n = costs.sum + 2 * costs.length + 2 ∧
      costs.sum ≤ budgetSum cost 0 (d.stacks p.counter).length := by
  obtain ⟨costs, n, e, hv, hei, hb⟩ :=
    visits_exists p body I cost stable spec (d.stacks p.counter) 0 d rfl hi
  rcases hv.bounds with ⟨hlen, he, hn⟩
  exact ⟨costs, n, e, hv, hv.eval, hlen, by simpa using hei, he, hn, hb⟩

theorem for_correct (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hi : I 0 d) :
    ∃ n e, StructuredCalls.Eval (forCmd p body) n d e ∧
      I (d.stacks p.counter).length e ∧ e.stacks p.counter = [] ∧
      n ≤ budgetSum cost 0 (d.stacks p.counter).length +
        2 * (d.stacks p.counter).length + 2 := by
  obtain ⟨costs, n, e, _, he, hlen, hei, hempty, hn, hb⟩ :=
    for_correct_measured p body I cost stable spec d hi
  refine ⟨n, e, he, hei, hempty, ?_⟩
  rw [hn, hlen]
  omega

@[simp] theorem size_forCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.size (forCmd p body) = StructuredCalls.size body + 3 := by
  simp [ StructuredCalls.size, StructuredProgram.size]
  omega

abbrev program (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (inputStack outputStack : Fin S) := StructuredCalls.compiled (forCmd p body) inputStack outputStack

theorem program_trace {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e)
    (inputStack outputStack : Fin S) :
    BitProgram.Trace (program p body inputStack outputStack) (n + 1)
      (d.withPC (some (program p body inputStack outputStack).entry)) (e.withPC none) :=
  StructuredCalls.compiled_halt_trace h.eval inputStack outputStack

end SubexponentialSAT.UnaryForPrograms

end OAI.Algorithms
