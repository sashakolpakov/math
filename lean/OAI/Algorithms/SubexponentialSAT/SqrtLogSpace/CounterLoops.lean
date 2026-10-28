import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Enumerators

/-! Actual binary counted loops whose invariant couples the current cursor to
remaining fuel. The invariant is transferred through the concrete decrement
and zero test, rather than through arbitrary changes to controller words. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CounterLoops

open BitProgram StructuredCalls CounterPrograms CounterForPrograms

/-- A measured callback can establish the next boundary invariant directly.
It is required only while the actual remaining counter value is positive. -/
theorem visits_exists_next {R S : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (spec : ∀ i d, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) →
      ∃ nb e, nb ≤ cost i ∧ Eval body nb d e ∧
        e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] ∧
        I (i + 1) (nextState p e)) (fuel : ℕ) :
    ∀ i d, value (d.stacks p.counter) = fuel → d.stacks p.scratch = [] →
      d.regs (p.register 2) = !(isZero (d.stacks p.counter)) → I i d →
      ∃ costs n e, Visits p body costs n d e ∧ I (i + fuel) e ∧
        e.stacks p.scratch = [] ∧ costs.sum ≤ budgetSum cost i fuel := by
  induction fuel with
  | zero =>
      intro i d hv hs hf hi
      have hz : isZero (d.stacks p.counter) = true := (isZero_eq_true_iff _).2 hv
      exact ⟨[], 1, d, .done d (by simpa [hz] using hf) hv,
        by simpa using hi, hs, by simp [budgetSum]⟩
  | succ fuel ih =>
      intro i d hv hs hf hi
      have hp : 0 < value (d.stacks p.counter) := by omega
      have hz : isZero (d.stacks p.counter) = false := (isZero_eq_false_iff _).2 hp
      have hf' : d.regs (p.register 2) = true := by simpa [hz] using hf
      obtain ⟨nb, e, hnb, he, hc, hes, hei⟩ := spec i d hi hs hp
      have hep : 0 < value (e.stacks p.counter) := by simpa only [hc] using hp
      have hn : value ((nextState p e).stacks p.counter) = fuel := by
        rw [nextState_counter, hc]
        have hd := value_decrement hep
        rw [hc, hv] at hd
        omega
      obtain ⟨costs, nt, f, ht, hfi, hfs, hbudget⟩ :=
        ih (i + 1) (nextState p e) hn (nextState_scratch ..) (nextState_flag ..) hei
      refine ⟨nb :: costs, (nb + advanceCost p e) + nt + 1, f,
        .step hf' hp he hc hes ht, ?_, hfs, ?_⟩
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hfi
      · simpa only [List.sum_cons, budgetSum] using Nat.add_le_add hnb hbudget

/-- The initial test is explicit. No hypothesis allows changing the counter
arbitrarily, so cursor/fuel relations and terminal width exceptions survive. -/
theorem for_correct_measured_next {R S : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (spec : ∀ i d, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) →
      ∃ nb e, nb ≤ cost i ∧ Eval body nb d e ∧
        e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] ∧
        I (i + 1) (nextState p e))
    (d : Data R S) (hs : d.stacks p.scratch = []) (hi : I 0 (testResult p d)) :
    ∃ costs n e, Eval (forCmd p body) n d e ∧
      (∃ loopSteps, Visits p body costs loopSteps (testResult p d) e ∧
        n = (8 * (d.stacks p.counter).length + 7) + loopSteps) ∧
      costs.length = value (d.stacks p.counter) ∧
      I (value (d.stacks p.counter)) e ∧ value (e.stacks p.counter) = 0 ∧
      (e.stacks p.counter).length = (d.stacks p.counter).length ∧
      e.stacks p.scratch = [] ∧
      costs.sum ≤ budgetSum cost 0 (value (d.stacks p.counter)) ∧
      n ≤ costs.sum + (value (d.stacks p.counter) + 1) *
        (16 * (d.stacks p.counter).length + 16) := by
  have hst := testResult_stacks p d hs
  obtain ⟨costs, nt, e, ht, hei, hes, hbudget⟩ :=
    visits_exists_next p body I cost spec (value (d.stacks p.counter)) 0
      (testResult p d) (by rw [hst]) (by rw [hst]; exact hs)
      (by rw [testResult_flag, hst]) hi
  rcases ht.bounds with ⟨hlen, hzero, hwidth, htime⟩
  rw [hst] at hlen hwidth htime
  refine ⟨costs, (8 * (d.stacks p.counter).length + 7) + nt, e,
    .seq (test_eval p d hs) ht.eval, ⟨nt, ht, rfl⟩, hlen,
    by simpa using hei, hzero, hwidth, hes, hbudget, ?_⟩
  rw [hlen] at htime
  calc
    8 * (d.stacks p.counter).length + 7 + nt ≤
        costs.sum + value (d.stacks p.counter) *
          (16 * (d.stacks p.counter).length + 16) +
          (16 * (d.stacks p.counter).length + 16) := by omega
    _ = costs.sum + (value (d.stacks p.counter) + 1) *
        (16 * (d.stacks p.counter).length + 16) := by ring

/-- Actual prefix space for the indexed invariant. The callback proves its
next boundary invariant through the concrete decrement, while every local
callback/controller prefix is bounded independently of numeric fuel. -/
theorem visits_stack_bound_next {R S : ℕ} (p : Ports R S) (body : Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ) (B D : ℕ)
    (spec : ∀ i d, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) →
      ∃ nb e, nb ≤ cost i ∧ Eval body nb d e ∧
        e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] ∧
        I (i + 1) (nextState p e))
    (hbound : ∀ i d, I i d → ∀ j, (d.stacks j).length ≤ B)
    (hcallback : ∀ i d e nb, I i d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.counter) → Eval body nb d e →
      (∀ j, (e.stacks j).length ≤ B) ∧
      ∀ q z, q ≤ nb → Trace (compiled body p.counter p.counter) q
        (d.withPC (some (compiled body p.counter p.counter).entry)) z →
        ∀ j, (z.stacks j).length ≤ D)
    {costs : List ℕ} {steps i : ℕ} {a b : Data R S}
    (hvis : Visits p body costs steps a b) (hI : I i a) (hs : a.stacks p.scratch = []) :
    ∀ q z, q ≤ steps → Trace (compiled (loopCmd p body) p.counter p.counter) q
      (a.withPC (some (compiled (loopCmd p body) p.counter p.counter).entry)) z →
      ∀ j, (z.stacks j).length ≤ max D (S * B + 16 * B + 16) := by
  let P := fun d : Data R S => ∃ i, I i d ∧ d.stacks p.scratch = []
  let Q := fun e : Data R S => (∃ i, I i (nextState p e)) ∧
    ∀ j, (e.stacks j).length ≤ B
  apply Enumerators.countdown_visits_stack_bound p body P Q B D _ _ _ _ hvis ⟨i, hI, hs⟩
  · intro d hd
    obtain ⟨i, hi, _⟩ := hd
    exact hbound i d hi
  · intro e he
    exact he.2
  · intro d e nb he hd _ hp
    obtain ⟨i, hi, hs⟩ := hd
    obtain ⟨nc, f, _, hf, _, _, hnext⟩ := spec i d hi hs hp
    have heq : e = f := Eval.final_unique p.counter he hf
    subst f
    obtain ⟨hb, hprefix⟩ := hcallback i d e nb hi hs hp he
    exact ⟨⟨⟨i + 1, hnext⟩, hb⟩, hprefix⟩
  · intro e he _
    obtain ⟨i, hi⟩ := he.1
    exact ⟨i, hi, nextState_scratch p e⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CounterLoops
