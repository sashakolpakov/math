import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# A finite binary-counted callback loop

The loop bound lives on a little-endian Boolean stack.  Fixed finite subroutines
perform zero testing and decrement, and an arbitrary fixed command is the loop
body.  The body may overwrite every register.  All measured evaluations below
compile to traces of a finite instruction table; proof-level state embeddings
are never used as executable instructions.
-/

namespace SubexponentialSAT.CounterForPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms

abbrev Data := StructuredProgram.State

/-- Fixed ports, independent of the represented counter value. -/
structure Ports (R S : ℕ) where
  register : Fin 3 ↪ Fin R
  counter : Fin S
  scratch : Fin S
  counter_ne_scratch : counter ≠ scratch

variable {R S : ℕ}

@[ext] theorem data_ext {a b : Data R S} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

def stackPorts (p : Ports R S) : Fin 2 ↪ Fin S where
  toFun i := if i = 0 then p.counter else p.scratch
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [p.counter_ne_scratch, Ne.symm p.counter_ne_scratch]

@[simp] theorem stackPorts_zero (p : Ports R S) : stackPorts p 0 = p.counter := rfl
@[simp] theorem stackPorts_one (p : Ports R S) : stackPorts p 1 = p.scratch := rfl

private theorem extend_restrict {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ h => congrArg g h) g a
  · exact Function.extend_apply' _ _ _ h

def localData (b present flag : Bool) (xs ys : List Bool) : Data 3 2 :=
  ⟨counterRegs b present flag, counterStacks xs ys⟩

noncomputable def install (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) : Data R S :=
  StructuredCalls.embedState p.register (stackPorts p) d (localData b present flag xs ys)

theorem install_self (p : Ports R S) (d : Data R S) :
    install p d (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter) (d.stacks p.scratch) = d := by
  apply data_ext
  · change Function.extend p.register
      (counterRegs (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2))) d.regs = d.regs
    have h : counterRegs (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2)) = d.regs ∘ p.register := by
      funext i
      fin_cases i <;> rfl
    rw [h, extend_restrict]
  · change Function.extend (stackPorts p)
      (counterStacks (d.stacks p.counter) (d.stacks p.scratch)) d.stacks = d.stacks
    have h : counterStacks (d.stacks p.counter) (d.stacks p.scratch) =
        d.stacks ∘ stackPorts p := by
      funext i
      fin_cases i <;> rfl
    rw [h, extend_restrict]

@[simp] theorem install_register (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) (i : Fin 3) :
    (install p d b present flag xs ys).regs (p.register i) =
      counterRegs b present flag i :=
  StructuredCalls.embedState_register _ _ _ _ p.register.injective i

@[simp] theorem install_counter (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) :
    (install p d b present flag xs ys).stacks p.counter = xs :=
  StructuredCalls.embedState_stack _ _ _ _ (stackPorts p).injective 0

@[simp] theorem install_scratch (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) :
    (install p d b present flag xs ys).stacks p.scratch = ys :=
  StructuredCalls.embedState_stack _ _ _ _ (stackPorts p).injective 1

theorem install_other_stack (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) (i : Fin S)
    (hc : i ≠ p.counter) (hs : i ≠ p.scratch) :
    (install p d b present flag xs ys).stacks i = d.stacks i := by
  apply StructuredCalls.embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact hc hj.symm
  · exact hs hj.symm

theorem install_stacks_self (p : Ports R S) (d : Data R S)
    (b present flag : Bool) (hs : d.stacks p.scratch = []) :
    (install p d b present flag (d.stacks p.counter) []).stacks = d.stacks := by
  have h := congrArg State.stacks (install_self p d)
  simpa only [install, StructuredCalls.embedState, localData, hs] using h

theorem ripple_local_trace (c b present flag : Bool) (xs : List Bool) :
    Trace (rippleProgram c) (rippleCost c xs + 1)
      ((localData b present flag xs []).withPC (some (rippleProgram c).entry))
      ((localData false false flag (ripple c xs) []).withPC none) := by
  have h : Trace (rippleProgram c) (rippleCost c xs)
      (counterCfg 0 b present flag xs [])
      (counterCfg 10 false false flag (ripple c xs) []) := by
    simpa using ripple_trace c b present flag xs []
  exact h.trans (.cons (by simp [step, counterCfg, execInstr,
    localData, State.withPC]) (.refl _))

theorem zero_local_trace (b present flag : Bool) (xs : List Bool) :
    Trace zeroProgram (8 * xs.length + 6)
      ((localData b present flag xs []).withPC (some zeroProgram.entry))
      ((localData false false (isZero xs) xs []).withPC none) := by
  have h : Trace zeroProgram (8 * xs.length + 5)
      (counterCfg 0 b present flag xs [])
      (counterCfg 9 false false (isZero xs) xs []) := by
    simpa [Nat.add_assoc] using
      SubexponentialSAT.Computation.Trace.cons (zero_step0 b present flag xs [])
        (zero_scan_trace b present true xs [])
  exact h.trans (.cons (by simp [step, counterCfg, execInstr,
    localData, State.withPC]) (.refl _))

abbrev decrementCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram (rippleProgram false) p.register (stackPorts p))

abbrev zeroCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram zeroProgram p.register (stackPorts p))

noncomputable def decrementResult (p : Ports R S) (d : Data R S) : Data R S :=
  install p d false false (d.regs (p.register 2)) (ripple false (d.stacks p.counter)) []

noncomputable def zeroResult (p : Ports R S) (d : Data R S) : Data R S :=
  install p d false false (isZero (d.stacks p.counter)) (d.stacks p.counter) []

theorem decrement_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (decrementCmd p) (rippleCost false (d.stacks p.counter) + 1)
      d (decrementResult p d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram false) p.register (stackPorts p) d
    p.register.injective (stackPorts p).injective
    (ripple_local_trace false (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (decrementCmd p) _
    (install p d _ _ _ _ []) (decrementResult p d) at h
  rw [← hs, install_self] at h
  exact h

theorem zero_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (zeroCmd p) (8 * (d.stacks p.counter).length + 6)
      d (zeroResult p d) := by
  have h := StructuredCalls.eval_call_lifted zeroProgram p.register (stackPorts p) d
    p.register.injective (stackPorts p).injective
    (zero_local_trace (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.counter))
  change StructuredCalls.Eval (zeroCmd p) _
    (install p d _ _ _ _ []) (zeroResult p d) at h
  rw [← hs, install_self] at h
  exact h

abbrev testCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (zeroCmd p) (.base (.atom (.bnot (p.register 2) (p.register 2))))

noncomputable def testResult (p : Ports R S) (d : Data R S) : Data R S :=
  (StructuredProgram.Atom.bnot (p.register 2) (p.register 2)).eval (zeroResult p d)

theorem test_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (testCmd p) (8 * (d.stacks p.counter).length + 7)
      d (testResult p d) := by
  have h := StructuredCalls.Eval.seq (zero_eval p d hs)
    (StructuredCalls.Eval.base (StructuredProgram.Eval.atom
      (.bnot (p.register 2) (p.register 2)) (zeroResult p d)))
  simpa only [testCmd, testResult, Nat.add_assoc] using h

@[simp] theorem testResult_flag (p : Ports R S) (d : Data R S) :
    (testResult p d).regs (p.register 2) = !(isZero (d.stacks p.counter)) := by
  simp only [testResult, Atom.eval, State.ofCfg, Atom.instr, execInstr, Function.update_self]
  simp [zeroResult]

theorem testResult_stacks (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) : (testResult p d).stacks = d.stacks := by
  change (zeroResult p d).stacks = d.stacks
  exact install_stacks_self p d _ _ _ hs

@[simp] theorem decrementResult_counter (p : Ports R S) (d : Data R S) :
    (decrementResult p d).stacks p.counter = ripple false (d.stacks p.counter) :=
  install_counter p d _ _ _ _ _

@[simp] theorem decrementResult_scratch (p : Ports R S) (d : Data R S) :
    (decrementResult p d).stacks p.scratch = [] := install_scratch p d _ _ _ _ _

abbrev advanceCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (decrementCmd p) (testCmd p)

noncomputable def nextState (p : Ports R S) (d : Data R S) : Data R S :=
  testResult p (decrementResult p d)

def advanceCost (p : Ports R S) (d : Data R S) : ℕ :=
  (rippleCost false (d.stacks p.counter) + 1) +
    (8 * (ripple false (d.stacks p.counter)).length + 7)

theorem advance_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (advanceCmd p) (advanceCost p d) d (nextState p d) := by
  have h := StructuredCalls.Eval.seq (decrement_eval p d hs)
    (test_eval p (decrementResult p d) (decrementResult_scratch ..))
  simpa only [advanceCmd, advanceCost, nextState, decrementResult_counter] using h

@[simp] theorem nextState_counter (p : Ports R S) (d : Data R S) :
    (nextState p d).stacks p.counter = ripple false (d.stacks p.counter) := by
  rw [nextState, testResult_stacks p _ (decrementResult_scratch ..), decrementResult_counter]

@[simp] theorem nextState_scratch (p : Ports R S) (d : Data R S) :
    (nextState p d).stacks p.scratch = [] := by
  rw [nextState, testResult_stacks p _ (decrementResult_scratch ..), decrementResult_scratch]

@[simp] theorem nextState_flag (p : Ports R S) (d : Data R S) :
    (nextState p d).regs (p.register 2) = !(isZero ((nextState p d).stacks p.counter)) := by
  rw [nextState, testResult_flag, testResult_stacks p _ (decrementResult_scratch ..)]

/-- State invariants may ignore every register and both controller stacks. -/
def OutsideEq (p : Ports R S) (a b : Data R S) : Prop :=
  ∀ j : Fin S, j ≠ p.counter → j ≠ p.scratch → a.stacks j = b.stacks j

def FrameStable (p : Ports R S) (I : ℕ → Data R S → Prop) : Prop :=
  ∀ i a b, OutsideEq p a b → I i a → I i b

theorem testResult_outside (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    OutsideEq p d (testResult p d) := by
  intro j _ _
  rw [testResult_stacks p d hs]

theorem nextState_outside (p : Ports R S) (d : Data R S) :
    OutsideEq p d (nextState p d) := by
  intro j hc hs
  rw [nextState, testResult_stacks p _ (decrementResult_scratch ..)]
  exact (install_other_stack p d _ _ _ _ _ j hc hs).symm

theorem advanceCost_le (p : Ports R S) (d : Data R S)
    (hp : 0 < value (d.stacks p.counter)) :
    advanceCost p d + 1 ≤ 16 * (d.stacks p.counter).length + 16 := by
  have hr := rippleCost_le false (d.stacks p.counter)
  have hl := decrement_length hp
  simp only [advanceCost, hl]
  omega

/-- The syntax is independent of the counter word and its value. -/
abbrev loopCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .while (p.register 2) (.seq body (advanceCmd p))

abbrev forCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .seq (testCmd p) (loopCmd p body)

/-- Each recorded cost comes from a real execution of the fixed callback. -/
inductive Visits (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    List ℕ → ℕ → Data R S → Data R S → Prop
  | done (d : Data R S) (hflag : d.regs (p.register 2) = false)
      (hzero : value (d.stacks p.counter) = 0) : Visits p body [] 1 d d
  | step {d e f : Data R S} {nb nt : ℕ} {costs : List ℕ}
      (hflag : d.regs (p.register 2) = true)
      (hpositive : 0 < value (d.stacks p.counter))
      (hbody : StructuredCalls.Eval body nb d e)
      (hcounter : e.stacks p.counter = d.stacks p.counter)
      (hscratch : e.stacks p.scratch = [])
      (tail : Visits p body costs nt (nextState p e) f) :
      Visits p body (nb :: costs) ((nb + advanceCost p e) + nt + 1) d f

theorem Visits.eval {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    StructuredCalls.Eval (loopCmd p body) n d e := by
  induction h with
  | done d hf hz => exact .while_false hf
  | step hf hp hb hc hs ht ih =>
      exact .while_true hf (.seq hb (advance_eval p _ hs)) ih

/-- A bound on callback costs, indexed by the number of preceding calls. -/
abbrev BodySpec (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ) : Prop :=
  ∀ i d, I i d → d.stacks p.scratch = [] → 0 < value (d.stacks p.counter) →
    ∃ nb e, nb ≤ cost i ∧ StructuredCalls.Eval body nb d e ∧
      e.stacks p.counter = d.stacks p.counter ∧ e.stacks p.scratch = [] ∧ I (i + 1) e

/-- Sum of the successive callback budgets; a specification, not program data. -/
abbrev budgetSum (cost : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | start, fuel + 1 => cost start + budgetSum cost (start + 1) fuel


/-- The recorded callback count is exactly the input value, and decrement
preserves the width of every positive counter representation. -/
theorem Visits.bounds {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {costs : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body costs n d e) :
    costs.length = value (d.stacks p.counter) ∧
      value (e.stacks p.counter) = 0 ∧
      (e.stacks p.counter).length = (d.stacks p.counter).length ∧
      n ≤ costs.sum + costs.length * (16 * (d.stacks p.counter).length + 16) + 1 := by
  induction h with
  | done d hf hz => exact ⟨hz.symm, hz, rfl, by simp⟩
  | @step d e f nb nt costs hf hp hb hc hs ht ih =>
      rcases ih with ⟨hlen, hzero, hwidth, htime⟩
      have hep : 0 < value (e.stacks p.counter) := by simpa only [hc] using hp
      have hdec := value_decrement hep
      have hw : ((nextState p e).stacks p.counter).length =
          (d.stacks p.counter).length := by
        rw [nextState_counter, decrement_length hep, hc]
      have hv : value ((nextState p e).stacks p.counter) + 1 =
          value (d.stacks p.counter) := by
        simpa only [nextState_counter, hc] using hdec
      have hcost := advanceCost_le p e hep
      rw [hc] at hcost
      rw [hw] at htime hwidth
      refine ⟨?_, hzero, hwidth, ?_⟩
      · simpa only [List.length_cons, hlen] using hv
      · simp only [List.sum_cons, List.length_cons]
        calc
          (nb + advanceCost p e) + nt + 1 ≤
              nb + (costs.sum + costs.length * (16 * (d.stacks p.counter).length + 16) + 1) +
                (16 * (d.stacks p.counter).length + 16) := by omega
          _ = nb + costs.sum + (costs.length + 1) *
                (16 * (d.stacks p.counter).length + 16) + 1 := by ring

/-- Every total callback satisfying its invariant has a measured loop trace.
The induction is on the value of the stack data, not on the finite control. -/
theorem visits_exists (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost) (fuel : ℕ) :
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
      have hni : I (i + 1) (nextState p e) := stable _ _ _ (nextState_outside p e) hei
      obtain ⟨costs, nt, f, ht, hfi, hfs, hbudget⟩ :=
        ih (i + 1) (nextState p e) hn (nextState_scratch ..) (nextState_flag ..) hni
      refine ⟨nb :: costs, (nb + advanceCost p e) + nt + 1, f,
        .step hf' hp he hc hes ht, ?_, hfs, ?_⟩
      · simpa only [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_left_comm,
          Nat.add_comm] using hfi
      · simpa only [List.sum_cons, budgetSum] using Nat.add_le_add hnb hbudget

/-- Complete measured execution, including an explicit record of the actual
callback costs.  The overhead is linear in the count times encoded width. -/
theorem for_correct_measured (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hs : d.stacks p.scratch = []) (hi : I 0 d) :
    ∃ costs n e, StructuredCalls.Eval (forCmd p body) n d e ∧
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
  have hit : I 0 (testResult p d) := stable _ _ _ (testResult_outside p d hs) hi
  obtain ⟨costs, nt, e, ht, hei, hes, hbudget⟩ :=
    visits_exists p body I cost stable spec (value (d.stacks p.counter)) 0
      (testResult p d) (by rw [hst]) (by rw [hst]; exact hs)
      (by rw [testResult_flag, hst]) hit
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

/-- Convenient interface with the sum of user-supplied callback budgets. -/
theorem for_correct (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hs : d.stacks p.scratch = []) (hi : I 0 d) :
    ∃ n e, StructuredCalls.Eval (forCmd p body) n d e ∧
      I (value (d.stacks p.counter)) e ∧ value (e.stacks p.counter) = 0 ∧
      (e.stacks p.counter).length = (d.stacks p.counter).length ∧
      e.stacks p.scratch = [] ∧
      n ≤ budgetSum cost 0 (value (d.stacks p.counter)) +
        (value (d.stacks p.counter) + 1) * (16 * (d.stacks p.counter).length + 16) := by
  obtain ⟨costs, n, e, he, _, _, hei, hz, hw, hs, hb, hn⟩ :=
    for_correct_measured p body I cost stable spec d hs hi
  exact ⟨n, e, he, hei, hz, hw, hs,
    hn.trans (Nat.add_le_add_right hb _)⟩

theorem budgetSum_le (cost : ℕ → ℕ) (start fuel bound : ℕ)
    (h : ∀ i, start ≤ i → i < start + fuel → cost i ≤ bound) :
    budgetSum cost start fuel ≤ fuel * bound := by
  induction fuel generalizing start with
  | zero => simp [budgetSum]
  | succ fuel ih =>
      have hs : cost start ≤ bound := h start le_rfl (by omega)
      have ht : budgetSum cost (start + 1) fuel ≤ fuel * bound :=
        ih (start + 1) (by intro i hlow hhigh; exact h i (by omega) (by omega))
      simpa [budgetSum, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hs ht

theorem budgetSum_le_mono (cost : ℕ → ℕ) (h : Monotone cost) (fuel : ℕ) :
    budgetSum cost 0 fuel ≤ fuel * cost fuel :=
  budgetSum_le cost 0 fuel (cost fuel) (fun _ _ hi => h (by omega))

theorem budgetSum_const (bound start fuel : ℕ) :
    budgetSum (fun _ => bound) start fuel = fuel * bound := by
  induction fuel generalizing start with
  | zero => simp [budgetSum]
  | succ fuel ih => simp [budgetSum, ih, Nat.succ_mul, Nat.add_comm]

/-- The control table grows only with the fixed callback program. -/
@[simp] theorem size_forCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.size (forCmd p body) = StructuredCalls.size body + 34 := by
  simp [
    StructuredCalls.size, StructuredProgram.size]
  omega

abbrev program (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (inputStack outputStack : Fin S) :
    Program R S (StructuredCalls.size (forCmd p body) + 1) :=
  StructuredCalls.compiled (forCmd p body) inputStack outputStack

/-- The counted loop's measured evaluation is an actual halted finite-table
trace, with one additional halt instruction. -/
theorem program_correct (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hs : d.stacks p.scratch = []) (hi : I 0 d)
    (inputStack outputStack : Fin S) :
    ∃ n e, Trace (program p body inputStack outputStack) (n + 1)
      (d.withPC (some (program p body inputStack outputStack).entry)) (e.withPC none) ∧
      I (value (d.stacks p.counter)) e ∧ value (e.stacks p.counter) = 0 ∧
      (e.stacks p.counter).length = (d.stacks p.counter).length ∧
      e.stacks p.scratch = [] ∧
      n ≤ budgetSum cost 0 (value (d.stacks p.counter)) +
        (value (d.stacks p.counter) + 1) * (16 * (d.stacks p.counter).length + 16) := by
  obtain ⟨n, e, he, hei, hz, hw, hes, hn⟩ := for_correct p body I cost stable spec d hs hi
  exact ⟨n, e, StructuredCalls.compiled_halt_trace he inputStack outputStack,
    hei, hz, hw, hes, hn⟩

/-- The existing verified compiler turns the same concrete loop into a
primitive finite-alphabet machine, with its fixed compilation overhead. -/
theorem primitive_correct (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (I : ℕ → Data R S → Prop) (cost : ℕ → ℕ)
    (stable : FrameStable p I) (spec : BodySpec p body I cost)
    (d : Data R S) (hs : d.stacks p.scratch = []) (hi : I 0 d)
    (inputStack outputStack : Fin S) :
    let machine := program p body inputStack outputStack
    ∃ e, Computation.RunsIn (BitProgram.primitive machine).step
      (BitProgram.primitiveOverhead machine *
        (budgetSum cost 0 (value (d.stacks p.counter)) +
          (value (d.stacks p.counter) + 1) * (16 * (d.stacks p.counter).length + 16) + 1))
      (BitProgram.primitiveCfg machine (d.withPC (some machine.entry)))
      (BitProgram.primitiveCfg machine (e.withPC none)) ∧
      I (value (d.stacks p.counter)) e ∧ value (e.stacks p.counter) = 0 ∧
      e.stacks p.scratch = [] := by
  obtain ⟨n, e, he, hei, hz, hw, hes, hn⟩ := for_correct p body I cost stable spec d hs hi
  refine ⟨e, ?_, hei, hz, hes⟩
  exact (StructuredCalls.primitive_execution he inputStack outputStack).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right hn 1))

end SubexponentialSAT.CounterForPrograms

end OAI.Algorithms
