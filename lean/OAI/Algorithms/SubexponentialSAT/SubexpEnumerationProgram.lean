import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# Encoded interval enumeration by fixed finite control

A current label and a remaining count live on little-endian Boolean stacks.
The program invokes an actual body command once per label and advances using
verified finite-table increment/decrement routines.  Mathematical state
embeddings below occur only in execution proofs; no instruction evaluates an
arbitrary semantic function.
-/

namespace SubexponentialSAT.SubexpEnumerationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open SubexponentialSAT.CounterPrograms

/-- Fixed counter ports, independent of all runtime binary values. -/
structure Ports (R S : ℕ) where
  register : Fin 3 ↪ Fin R
  current : Fin S
  remaining : Fin S
  scratch : Fin S
  current_ne_remaining : current ≠ remaining
  current_ne_scratch : current ≠ scratch
  remaining_ne_scratch : remaining ≠ scratch

variable {R S : ℕ}

abbrev Data := StructuredProgram.State

@[ext] theorem data_ext {a b : Data R S} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

def target (p : Ports R S) (useCurrent : Bool) : Fin S :=
  if useCurrent then p.current else p.remaining

theorem target_ne_scratch (p : Ports R S) (useCurrent : Bool) :
    target p useCurrent ≠ p.scratch := by
  cases useCurrent
  · exact p.remaining_ne_scratch
  · exact p.current_ne_scratch

def stackPorts (p : Ports R S) (useCurrent : Bool) : Fin 2 ↪ Fin S where
  toFun i := if i = 0 then target p useCurrent else p.scratch
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [target_ne_scratch p useCurrent,
      Ne.symm (target_ne_scratch p useCurrent)]

@[simp] theorem stackPorts_zero (p : Ports R S) (q : Bool) :
    stackPorts p q 0 = target p q := rfl
@[simp] theorem stackPorts_one (p : Ports R S) (q : Bool) :
    stackPorts p q 1 = p.scratch := rfl

private theorem extend_restrict {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact (Function.FactorsThrough.extend_apply (fun _ _ h => congrArg g h) g a)
  · exact Function.extend_apply' _ _ _ h

def localData (b present flag : Bool) (xs ys : List Bool) : Data 3 2 :=
  ⟨counterRegs b present flag, counterStacks xs ys⟩

/-- A proof-level frame embedding; executable code uses only its fixed port maps. -/
noncomputable def install (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) : Data R S :=
  StructuredCalls.embedState p.register (stackPorts p q) d (localData b present flag xs ys)

theorem install_self (p : Ports R S) (q : Bool) (d : Data R S) :
    install p q d (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks (target p q)) (d.stacks p.scratch) = d := by
  apply data_ext
  · change Function.extend p.register
      (counterRegs (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2))) d.regs = d.regs
    have h : counterRegs (d.regs (p.register 0)) (d.regs (p.register 1))
        (d.regs (p.register 2)) = d.regs ∘ p.register := by
      funext i
      fin_cases i <;> rfl
    rw [h, extend_restrict]
  · change Function.extend (stackPorts p q)
      (counterStacks (d.stacks (target p q)) (d.stacks p.scratch)) d.stacks = d.stacks
    have h : counterStacks (d.stacks (target p q)) (d.stacks p.scratch) =
        d.stacks ∘ stackPorts p q := by
      funext i
      fin_cases i <;> rfl
    rw [h, extend_restrict]

@[simp] theorem install_register (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) (i : Fin 3) :
    (install p q d b present flag xs ys).regs (p.register i) =
      counterRegs b present flag i :=
  StructuredCalls.embedState_register _ _ _ _ p.register.injective i

@[simp] theorem install_target (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) :
    (install p q d b present flag xs ys).stacks (target p q) = xs :=
  StructuredCalls.embedState_stack _ _ _ _ (stackPorts p q).injective 0

@[simp] theorem install_scratch (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) :
    (install p q d b present flag xs ys).stacks p.scratch = ys :=
  StructuredCalls.embedState_stack _ _ _ _ (stackPorts p q).injective 1

theorem install_other_stack (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) (i : Fin S)
    (ht : i ≠ target p q) (hs : i ≠ p.scratch) :
    (install p q d b present flag xs ys).stacks i = d.stacks i := by
  apply StructuredCalls.embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact ht hj.symm
  · exact hs hj.symm

theorem install_other_register (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (xs ys : List Bool) (i : Fin R)
    (hi : ∀ j, p.register j ≠ i) :
    (install p q d b present flag xs ys).regs i = d.regs i := by
  apply StructuredCalls.embedState_register_frame
  rintro ⟨j, hj⟩
  exact hi j hj

/-- Actual complete carry/borrow trace, preserving the caller's flag bit. -/
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

/-- Actual scan/restore trace, including the final halt instruction. -/
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

abbrev rippleCmd (p : Ports R S) (q c : Bool) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram (rippleProgram c) p.register (stackPorts p q))

abbrev zeroCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .call (ProgramLinking.liftProgram zeroProgram p.register (stackPorts p false))

noncomputable def rippleResult (p : Ports R S) (q c : Bool) (d : Data R S) : Data R S :=
  install p q d false false (d.regs (p.register 2))
    (ripple c (d.stacks (target p q))) []

noncomputable def zeroResult (p : Ports R S) (d : Data R S) : Data R S :=
  install p false d false false (isZero (d.stacks p.remaining)) (d.stacks p.remaining) []

theorem ripple_eval (p : Ports R S) (q c : Bool) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (rippleCmd p q c) (rippleCost c (d.stacks (target p q)) + 1)
      d (rippleResult p q c d) := by
  have h := StructuredCalls.eval_call_lifted (rippleProgram c) p.register (stackPorts p q) d
    p.register.injective (stackPorts p q).injective
    (ripple_local_trace c (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks (target p q)))
  change StructuredCalls.Eval (rippleCmd p q c) _
    (install p q d _ _ _ _ []) (rippleResult p q c d) at h
  rw [← hs, install_self] at h
  exact h

theorem zero_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (zeroCmd p) (8 * (d.stacks p.remaining).length + 6)
      d (zeroResult p d) := by
  have h := StructuredCalls.eval_call_lifted zeroProgram p.register (stackPorts p false) d
    p.register.injective (stackPorts p false).injective
    (zero_local_trace (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.remaining))
  change StructuredCalls.Eval (zeroCmd p) _
    (install p false d _ _ _ _ []) (zeroResult p d) at h
  have hd : install p false d (d.regs (p.register 0)) (d.regs (p.register 1))
      (d.regs (p.register 2)) (d.stacks p.remaining) [] = d := by
    simpa [target, hs] using install_self p false d
  rw [hd] at h
  exact h

theorem install_stacks_self (p : Ports R S) (q : Bool) (d : Data R S)
    (b present flag : Bool) (hs : d.stacks p.scratch = []) :
    (install p q d b present flag (d.stacks (target p q)) []).stacks = d.stacks := by
  have h := congrArg State.stacks (install_self p q d)
  simpa only [install, StructuredCalls.embedState, localData, hs] using h

abbrev testCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (zeroCmd p) (.base (.atom (.bnot (p.register 2) (p.register 2))))

noncomputable def testResult (p : Ports R S) (d : Data R S) : Data R S :=
  (StructuredProgram.Atom.bnot (p.register 2) (p.register 2)).eval (zeroResult p d)

theorem test_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (testCmd p) (8 * (d.stacks p.remaining).length + 7)
      d (testResult p d) := by
  have h := StructuredCalls.Eval.seq (zero_eval p d hs)
    (StructuredCalls.Eval.base (StructuredProgram.Eval.atom
      (.bnot (p.register 2) (p.register 2)) (zeroResult p d)))
  simpa only [testCmd, testResult, Nat.add_assoc] using h

@[simp] theorem testResult_flag (p : Ports R S) (d : Data R S) :
    (testResult p d).regs (p.register 2) = !(isZero (d.stacks p.remaining)) := by
  simp only [testResult, Atom.eval, State.ofCfg, Atom.instr, execInstr, Function.update_self]
  simp [zeroResult]

theorem testResult_stacks (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) : (testResult p d).stacks = d.stacks := by
  change (zeroResult p d).stacks = d.stacks
  exact install_stacks_self p false d _ _ _ hs

@[simp] theorem rippleResult_target (p : Ports R S) (q c : Bool) (d : Data R S) :
    (rippleResult p q c d).stacks (target p q) = ripple c (d.stacks (target p q)) := by
  exact install_target p q d _ _ _ _ _

@[simp] theorem rippleResult_scratch (p : Ports R S) (q c : Bool) (d : Data R S) :
    (rippleResult p q c d).stacks p.scratch = [] := by
  exact install_scratch p q d _ _ _ _ _

theorem rippleResult_other (p : Ports R S) (q c : Bool) (d : Data R S)
    (i : Fin S) (ht : i ≠ target p q) (hs : i ≠ p.scratch) :
    (rippleResult p q c d).stacks i = d.stacks i :=
  install_other_stack p q d _ _ _ _ _ i ht hs

abbrev advanceCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (rippleCmd p true true) (rippleCmd p false false)

noncomputable def advanceResult (p : Ports R S) (d : Data R S) : Data R S :=
  rippleResult p false false (rippleResult p true true d)

def advanceCost (p : Ports R S) (d : Data R S) : ℕ :=
  (rippleCost true (d.stacks p.current) + 1) +
    (rippleCost false (d.stacks p.remaining) + 1)

theorem advance_eval (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (advanceCmd p) (advanceCost p d) d (advanceResult p d) := by
  have hrem : (rippleResult p true true d).stacks p.remaining = d.stacks p.remaining :=
    rippleResult_other p true true d p.remaining (Ne.symm p.current_ne_remaining)
      p.remaining_ne_scratch
  have h := StructuredCalls.Eval.seq (ripple_eval p true true d hs)
    (ripple_eval p false false (rippleResult p true true d) (rippleResult_scratch ..))
  simpa only [target, Bool.false_eq_true, ite_false, ite_true, hrem, advanceCmd,
    advanceCost, advanceResult] using h

@[simp] theorem advanceResult_current (p : Ports R S) (d : Data R S) :
    (advanceResult p d).stacks p.current = ripple true (d.stacks p.current) := by
  rw [advanceResult, rippleResult_other p false false _ p.current
    p.current_ne_remaining p.current_ne_scratch]
  exact rippleResult_target p true true d

@[simp] theorem advanceResult_remaining (p : Ports R S) (d : Data R S) :
    (advanceResult p d).stacks p.remaining = ripple false (d.stacks p.remaining) := by
  change (rippleResult p false false _).stacks (target p false) = _
  rw [rippleResult_target]
  change ripple false ((rippleResult p true true d).stacks p.remaining) = _
  rw [rippleResult_other p true true _ p.remaining
    (Ne.symm p.current_ne_remaining) p.remaining_ne_scratch]

@[simp] theorem advanceResult_scratch (p : Ports R S) (d : Data R S) :
    (advanceResult p d).stacks p.scratch = [] := rippleResult_scratch ..

abbrev advanceTestCmd (p : Ports R S) : StructuredCalls.Cmd R S :=
  .seq (advanceCmd p) (testCmd p)

noncomputable def nextState (p : Ports R S) (d : Data R S) : Data R S :=
  testResult p (advanceResult p d)

def advanceTestCost (p : Ports R S) (d : Data R S) : ℕ :=
  advanceCost p d + (8 * (ripple false (d.stacks p.remaining)).length + 7)

theorem advanceTest_eval (p : Ports R S) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (advanceTestCmd p) (advanceTestCost p d) d (nextState p d) := by
  have h := StructuredCalls.Eval.seq (advance_eval p d hs)
    (test_eval p (advanceResult p d) (advanceResult_scratch ..))
  simpa only [advanceTestCmd, advanceTestCost, nextState, advanceResult_remaining] using h

@[simp] theorem nextState_current (p : Ports R S) (d : Data R S) :
    (nextState p d).stacks p.current = ripple true (d.stacks p.current) := by
  rw [nextState, testResult_stacks p _ (advanceResult_scratch ..), advanceResult_current]
@[simp] theorem nextState_remaining (p : Ports R S) (d : Data R S) :
    (nextState p d).stacks p.remaining = ripple false (d.stacks p.remaining) := by
  rw [nextState, testResult_stacks p _ (advanceResult_scratch ..), advanceResult_remaining]
@[simp] theorem nextState_scratch (p : Ports R S) (d : Data R S) :
    (nextState p d).stacks p.scratch = [] := by
  rw [nextState, testResult_stacks p _ (advanceResult_scratch ..), advanceResult_scratch]
@[simp] theorem nextState_flag (p : Ports R S) (d : Data R S) :
    (nextState p d).regs (p.register 2) =
      !(isZero ((nextState p d).stacks p.remaining)) := by
  rw [nextState, testResult_flag, testResult_stacks p _ (advanceResult_scratch ..)]

/-- Fixed finite control; all growth is in stacks, never in this syntax. -/
abbrev loopCmd (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .while (p.register 2) (.seq body (advanceTestCmd p))

abbrev enumerate (p : Ports R S) (body : StructuredCalls.Cmd R S) : StructuredCalls.Cmd R S :=
  .seq (testCmd p) (loopCmd p body)

/-- An observation of the actual body entries. Each constructor contains a
real body execution, and the controller transitions are the checked routines. -/
inductive Visits (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    List ℕ → ℕ → Data R S → Data R S → Prop
  | done (d : Data R S) (hflag : d.regs (p.register 2) = false) :
      Visits p body [] 1 d d
  | step {d e f : Data R S} {nb nt : ℕ} {labels : List ℕ}
      (hflag : d.regs (p.register 2) = true)
      (hbody : StructuredCalls.Eval body nb d e)
      (hcurrent : e.stacks p.current = d.stacks p.current)
      (hremaining : e.stacks p.remaining = d.stacks p.remaining)
      (hscratch : e.stacks p.scratch = [])
      (tail : Visits p body labels nt (nextState p e) f) :
      Visits p body (value (d.stacks p.current) :: labels)
        ((nb + advanceTestCost p e) + nt + 1) d f

theorem Visits.eval {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {labels : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body labels n d e) :
    StructuredCalls.Eval (loopCmd p body) n d e := by
  induction h with
  | done d hf => exact .while_false hf
  | step hf hb hc hr hs ht ih =>
      exact .while_true hf (.seq hb (advanceTest_eval p _ hs)) ih

/-- A callback specification consists of actual finite program executions.
It may change every unreserved register/stack, but preserves the two counters. -/
abbrev BodyTotal (p : Ports R S) (body : StructuredCalls.Cmd R S) : Prop :=
  ∀ d : Data R S, d.stacks p.scratch = [] →
    ∃ nb e, StructuredCalls.Eval body nb d e ∧
      e.stacks p.current = d.stacks p.current ∧
      e.stacks p.remaining = d.stacks p.remaining ∧ e.stacks p.scratch = []

theorem visits_exists (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (hb : BodyTotal p body) (fuel : ℕ) :
    ∀ d : Data R S, value (d.stacks p.remaining) = fuel →
      d.stacks p.scratch = [] →
      d.regs (p.register 2) = !(isZero (d.stacks p.remaining)) →
      ∃ n e, Visits p body (List.range' (value (d.stacks p.current)) fuel) n d e ∧
        value (e.stacks p.current) = value (d.stacks p.current) + fuel ∧
        value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  induction fuel with
  | zero =>
      intro d hv hs hf
      have hz : isZero (d.stacks p.remaining) = true := (isZero_eq_true_iff _).2 hv
      refine ⟨1, d, ?_, by simp, hv, hs⟩
      simpa using Visits.done d (by simpa [hz] using hf)
  | succ fuel ih =>
      intro d hv hs hf
      have hp : 0 < value (d.stacks p.remaining) := by omega
      have hz : isZero (d.stacks p.remaining) = false := (isZero_eq_false_iff _).2 hp
      have hf' : d.regs (p.register 2) = true := by simpa [hz] using hf
      obtain ⟨nb, e, he, hc, hr, heScratch⟩ := hb d hs
      have hep : 0 < value (e.stacks p.remaining) := by simpa [hr] using hp
      have hnext : value ((nextState p e).stacks p.remaining) = fuel := by
        rw [nextState_remaining]
        have hdec := value_decrement hep
        have hevalue : value (e.stacks p.remaining) = fuel + 1 := by rw [hr, hv]
        omega
      have hcurrent : value ((nextState p e).stacks p.current) =
          value (d.stacks p.current) + 1 := by
        rw [nextState_current, value_increment, hc]
      obtain ⟨nt, f, ht, hfc, hfr, hfs⟩ :=
        ih (nextState p e) hnext (nextState_scratch ..) (nextState_flag ..)
      refine ⟨(nb + advanceTestCost p e) + nt + 1, f, ?_, ?_, hfr, hfs⟩
      · simpa only [List.range'_succ, hcurrent] using
          Visits.step hf' he hc hr heScratch ht
      · rw [hcurrent] at hfc
        omega

/-- Every input has an actual execution whose body-entry observations are
exactly the requested consecutive labels, with no omission or duplication. -/
theorem enumerate_correct (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (hb : BodyTotal p body) (d : Data R S) (hs : d.stacks p.scratch = []) :
    ∃ n e, StructuredCalls.Eval (enumerate p body) n d e ∧
      (∃ loopSteps, Visits p body
        (List.range' (value (d.stacks p.current)) (value (d.stacks p.remaining)))
        loopSteps (testResult p d) e) ∧
      value (e.stacks p.current) = value (d.stacks p.current) + value (d.stacks p.remaining) ∧
      value (e.stacks p.remaining) = 0 ∧ e.stacks p.scratch = [] := by
  have hst := testResult_stacks p d hs
  obtain ⟨n, e, he, hc, hr, hscratch⟩ := visits_exists p body hb
    (value (d.stacks p.remaining)) (testResult p d) (by rw [hst])
      (by rw [hst]; exact hs) (by rw [testResult_flag, hst])
  refine ⟨(8 * (d.stacks p.remaining).length + 7) + n, e,
    .seq (test_eval p d hs) he.eval, ?_, ?_, hr, hscratch⟩
  · exact ⟨n, by simpa only [hst] using he⟩
  · simpa only [hst] using hc

theorem testResult_other_register (p : Ports R S) (d : Data R S) (i : Fin R)
    (hi : ∀ j, p.register j ≠ i) : (testResult p d).regs i = d.regs i := by
  simp only [testResult, Atom.eval, State.ofCfg, Atom.instr, execInstr ]
  rw [Function.update_of_ne (Ne.symm (hi 2))]
  exact install_other_register p false d _ _ _ _ _ i hi

theorem rippleResult_other_register (p : Ports R S) (q c : Bool) (d : Data R S)
    (i : Fin R) (hi : ∀ j, p.register j ≠ i) :
    (rippleResult p q c d).regs i = d.regs i :=
  install_other_register p q d _ _ _ _ _ i hi

theorem nextState_other_register (p : Ports R S) (d : Data R S) (i : Fin R)
    (hi : ∀ j, p.register j ≠ i) : (nextState p d).regs i = d.regs i := by
  rw [nextState, testResult_other_register p _ i hi, advanceResult,
    rippleResult_other_register p false false _ i hi,
    rippleResult_other_register p true true _ i hi]

theorem testResult_other_stack (p : Ports R S) (d : Data R S) (i : Fin S)
    (hr : i ≠ p.remaining) (hs : i ≠ p.scratch) :
    (testResult p d).stacks i = d.stacks i := by
  change (zeroResult p d).stacks i = d.stacks i
  exact install_other_stack p false d _ _ _ _ _ i hr hs

theorem nextState_other_stack (p : Ports R S) (d : Data R S) (i : Fin S)
    (hc : i ≠ p.current) (hr : i ≠ p.remaining) (hs : i ≠ p.scratch) :
    (nextState p d).stacks i = d.stacks i := by
  rw [nextState, testResult_other_stack p _ i hr hs, advanceResult,
    rippleResult_other p false false _ i hr hs,
    rippleResult_other p true true _ i hc hs]

/-- An external Boolean result flag folds the actual callback tests in visit
order. The controller never reads or changes this unreserved flag. -/
theorem Visits.flag_fold {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {labels : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body labels n d e)
    (flag : Fin R) (hf : ∀ j, p.register j ≠ flag) (test : ℕ → Bool)
    (hb : ∀ nb a b, StructuredCalls.Eval body nb a b →
      b.regs flag = (a.regs flag && test (value (a.stacks p.current)))) :
    e.regs flag = (d.regs flag && labels.all test) := by
  induction h with
  | done d hd => simp
  | @step d a e nb nt labels hd hbody hc hr hs ht ih =>
      rw [ih, nextState_other_register p a flag hf, hb nb d a hbody]
      simp only [List.all_cons, Bool.and_assoc]

/-- Invariant-aware form for callbacks whose correctness needs a fixed
candidate word, a positive divisor, or other preserved caller data. -/
theorem Visits.flag_fold_of_invariant {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {labels : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body labels n d e)
    (flag : Fin R) (hf : ∀ j, p.register j ≠ flag) (test : ℕ → Bool)
    (P : Data R S → Prop) (hP : P d)
    (hb : ∀ nb a b, StructuredCalls.Eval body nb a b → P a →
      P b ∧ b.regs flag = (a.regs flag && test (value (a.stacks p.current))))
    (hn : ∀ a, P a → P (nextState p a)) :
    P e ∧ e.regs flag = (d.regs flag && labels.all test) := by
  induction h with
  | done d hd => exact ⟨hP, by simp⟩
  | @step d a e nb nt labels hd hbody hc hr hs ht ih =>
      obtain ⟨ha, hflag⟩ := hb nb d a hbody hP
      obtain ⟨he, hfold⟩ := ih (hn a ha)
      refine ⟨he, ?_⟩
      rw [hfold, nextState_other_register p a flag hf, hflag]
      simp only [List.all_cons, Bool.and_assoc]

theorem Visits.stack_preserved {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {labels : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body labels n d e)
    (i : Fin S) (hc : i ≠ p.current) (hr : i ≠ p.remaining) (hs : i ≠ p.scratch)
    (hb : ∀ nb a b, StructuredCalls.Eval body nb a b → b.stacks i = a.stacks i) :
    e.stacks i = d.stacks i := by
  induction h with
  | done => rfl
  | @step d a e nb nt labels hd hbody hcur hrem hscr ht ih =>
      rw [ih, nextState_other_stack p a i hc hr hs, hb nb d a hbody]

/-- Prepending each computed row to an unreserved output stack records rows
in reverse visit order. Every row equation concerns an actual body execution. -/
theorem Visits.output_fold {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {labels : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body labels n d e)
    (output : Fin S) (hc : output ≠ p.current) (hr : output ≠ p.remaining)
    (hs : output ≠ p.scratch) (emit : ℕ → List Bool)
    (hb : ∀ nb a b, StructuredCalls.Eval body nb a b →
      b.stacks output = emit (value (a.stacks p.current)) ++ a.stacks output) :
    e.stacks output = labels.reverse.flatMap emit ++ d.stacks output := by
  induction h with
  | done => simp
  | @step d a e nb nt labels hd hbody hcur hrem hscr ht ih =>
      rw [ih, nextState_other_stack p a output hc hr hs, hb nb d a hbody]
      simp only [List.reverse_cons, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]

/-- The row-fold theorem with a preserved caller invariant, for fixed clause,
width, or lookup data needed to prove the actual row evaluator correct. -/
theorem Visits.output_fold_of_invariant {p : Ports R S}
    {body : StructuredCalls.Cmd R S} {labels : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p body labels n d e)
    (output : Fin S) (hc : output ≠ p.current) (hr : output ≠ p.remaining)
    (hs : output ≠ p.scratch) (emit : ℕ → List Bool)
    (P : Data R S → Prop) (hP : P d)
    (hb : ∀ nb a b, StructuredCalls.Eval body nb a b → P a →
      P b ∧ b.stacks output = emit (value (a.stacks p.current)) ++ a.stacks output)
    (hn : ∀ a, P a → P (nextState p a)) :
    P e ∧ e.stacks output = labels.reverse.flatMap emit ++ d.stacks output := by
  induction h with
  | done => exact ⟨hP, by simp⟩
  | @step d a e nb nt labels hd hbody hcur hrem hscr ht ih =>
      obtain ⟨ha, hout⟩ := hb nb d a hbody hP
      obtain ⟨he, hfold⟩ := ih (hn a ha)
      refine ⟨he, ?_⟩
      rw [hfold, nextState_other_stack p a output hc hr hs, hout]
      simp only [List.reverse_cons, List.flatMap_append, List.flatMap_singleton,
        List.append_assoc]

/-- Exact static control size; none of the binary input values occurs here. -/
theorem enumerate_size (p : Ports R S) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.size (enumerate p body) = StructuredCalls.size body + 45 := by
  simp [ StructuredCalls.size, StructuredProgram.size]
  omega

abbrev program (p : Ports R S) (body : StructuredCalls.Cmd R S) :=
  StructuredCalls.compiled (enumerate p body) p.remaining p.current

/-- Every structured execution above is an execution of its actual finite
instruction table, including the terminal halt. -/
theorem program_trace (p : Ports R S) (body : StructuredCalls.Cmd R S)
    {n : ℕ} {d e : Data R S} (h : StructuredCalls.Eval (enumerate p body) n d e) :
    Trace (program p body) (n + 1)
      (d.withPC (some (program p body).entry)) (e.withPC none) :=
  StructuredCalls.compiled_halt_trace h p.remaining p.current

theorem program_primitive (p : Ports R S) (body : StructuredCalls.Cmd R S)
    {n : ℕ} {d e : Data R S} (h : StructuredCalls.Eval (enumerate p body) n d e) :
    Computation.RunsIn (BitProgram.primitive (program p body)).step
      (BitProgram.primitiveOverhead (program p body) * (n + 1))
      (BitProgram.primitiveCfg (program p body) (d.withPC (some (program p body).entry)))
      (BitProgram.primitiveCfg (program p body) (e.withPC none)) :=
  StructuredCalls.primitive_execution h p.remaining p.current

theorem skip_body_total (p : Ports R S) : BodyTotal p (.base .skip) := by
  intro d hs
  exact ⟨0, d, .base (.skip d), rfl, rfl, hs⟩

/-- A concrete body with no external correctness assumption: the generated
table traverses the whole encoded interval and ends with its successor. -/
theorem skip_enumeration (p : Ports R S) (d : Data R S) (hs : d.stacks p.scratch = []) :
    ∃ (n : ℕ) (e : Data R S), Trace (program p (.base .skip)) (n + 1)
      (d.withPC (some (program p (.base .skip)).entry)) (e.withPC none) ∧
      value (e.stacks p.current) = value (d.stacks p.current) + value (d.stacks p.remaining) ∧
      value (e.stacks p.remaining) = 0 := by
  obtain ⟨n, e, he, hvisits, hc, hr, hs⟩ :=
    enumerate_correct p (.base .skip) (skip_body_total p) d hs
  exact ⟨n, e, program_trace p (.base .skip) he, hc, hr⟩

theorem advanceTestCost_le (p : Ports R S) (d : Data R S)
    (hp : 0 < value (d.stacks p.remaining)) :
    advanceTestCost p d ≤
      8 * (d.stacks p.current).length + 16 * (d.stacks p.remaining).length + 23 := by
  have hc := rippleCost_le true (d.stacks p.current)
  have hr := rippleCost_le false (d.stacks p.remaining)
  unfold advanceTestCost advanceCost
  rw [decrement_length hp]
  omega

/-- An explicit instruction bound for a recorded traversal. `C` bounds actual
callback evaluations; `L` and `M` bound the current and remaining word widths. -/
theorem Visits.steps_le {p : Ports R S} {body : StructuredCalls.Cmd R S}
    {labels : List ℕ} {n : ℕ} {d e : Data R S} (h : Visits p body labels n d e)
    (C L M : ℕ)
    (hb : ∀ nb a b, StructuredCalls.Eval body nb a b → nb ≤ C)
    (hcount : value (d.stacks p.remaining) = labels.length)
    (hcurrent : (d.stacks p.current).length + labels.length ≤ L)
    (hremaining : (d.stacks p.remaining).length ≤ M) :
    n ≤ labels.length * (C + 8 * L + 16 * M + 24) + 1 := by
  induction h generalizing L M with
  | done d hf => simp
  | @step d a e nb nt labels hf hbody hcur hrem hscratch htail ih =>
      have hp : 0 < value (a.stacks p.remaining) := by
        rw [hrem, hcount]
        simp
      have hnextcount : value ((nextState p a).stacks p.remaining) = labels.length := by
        rw [nextState_remaining]
        have hv := value_decrement hp
        have ha : value (a.stacks p.remaining) = labels.length + 1 := by
          simpa [hrem] using hcount
        omega
      have hnextcurrent : ((nextState p a).stacks p.current).length + labels.length ≤ L := by
        rw [nextState_current, hcur]
        have hw := ripple_length_le true (a.stacks p.current)
        rw [hcur] at hw
        simp only [List.length_cons] at hcurrent
        omega
      have hnextremaining : ((nextState p a).stacks p.remaining).length ≤ M := by
        rw [nextState_remaining, decrement_length hp, hrem]
        exact hremaining
      have hit := ih L M hnextcount hnextcurrent hnextremaining
      have hcost := advanceTestCost_le p a hp
      have hwidth : (a.stacks p.current).length ≤ L := by
        rw [hcur]
        simp only [List.length_cons] at hcurrent
        omega
      have hwidth' : (a.stacks p.remaining).length ≤ M := by simpa [hrem] using hremaining
      have hnb := hb nb d a hbody
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- A uniform bound with all growing encoded widths and the callback cost
visible. Leading zeroes are allowed in both counters. -/
theorem enumerate_bounded (p : Ports R S) (body : StructuredCalls.Cmd R S)
    (htotal : BodyTotal p body) (C : ℕ)
    (hbody : ∀ nb a b, StructuredCalls.Eval body nb a b → nb ≤ C)
    (d : Data R S) (hs : d.stacks p.scratch = []) :
    ∃ n e, StructuredCalls.Eval (enumerate p body) n d e ∧
      n ≤ 8 * (d.stacks p.remaining).length + 8 + value (d.stacks p.remaining) *
        (C + 8 * ((d.stacks p.current).length + value (d.stacks p.remaining)) +
          16 * (d.stacks p.remaining).length + 24) ∧
      value (e.stacks p.current) = value (d.stacks p.current) + value (d.stacks p.remaining) ∧
      value (e.stacks p.remaining) = 0 := by
  have hst := testResult_stacks p d hs
  obtain ⟨n, e, he, hc, hr, hscratch⟩ := visits_exists p body htotal
    (value (d.stacks p.remaining)) (testResult p d) (by rw [hst])
      (by rw [hst]; exact hs) (by rw [testResult_flag, hst])
  have hn := he.steps_le C
    ((d.stacks p.current).length + value (d.stacks p.remaining))
    (d.stacks p.remaining).length hbody (by simp [hst]) (by simp [hst]) (by simp [hst])
  simp only [List.length_range'] at hn
  refine ⟨(8 * (d.stacks p.remaining).length + 7) + n, e,
    .seq (test_eval p d hs) he.eval, ?_, ?_, hr⟩
  · omega
  · simpa only [hst] using hc

end SubexponentialSAT.SubexpEnumerationProgram

end OAI.Algorithms
