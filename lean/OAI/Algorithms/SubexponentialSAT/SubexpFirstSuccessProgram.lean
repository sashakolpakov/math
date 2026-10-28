import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationProgram
import OAI.Algorithms.SubexponentialSAT.ParameterOrder

namespace OAI.Algorithms

/-!
# First-success search by fixed finite control

The current label and remaining count are binary stacks. The callback is an
actual fixed structured command (in particular it may call a finite bit
program). A Boolean test used in correctness statements is never an instruction
or an argument of the executable program. The success bit is cleared on entry,
so even an empty interval has a defined negative result.
-/

namespace SubexponentialSAT.SubexpFirstSuccessProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms
open SubexponentialSAT.SubexpEnumerationProgram

variable {R S : ℕ}

abbrev clearCmd (success : Fin R) : StructuredCalls.Cmd R S :=
  .base (.atom (.set success false))

def clearState (success : Fin R) (d : Data R S) : Data R S :=
  (Atom.set success false).eval d

@[simp] theorem clearState_stacks (success : Fin R) (d : Data R S) :
    (clearState success d).stacks = d.stacks := rfl

@[simp] theorem clearState_flag (success : Fin R) (d : Data R S) :
    (clearState success d).regs success = false := by
  simp [clearState, Atom.eval, Atom.instr, State.ofCfg,
    execInstr, Function.update_self]

theorem clearState_other_register (success i : Fin R) (d : Data R S)
    (hi : i ≠ success) : (clearState success d).regs i = d.regs i := by
  simp [clearState, Atom.eval, Atom.instr, State.ofCfg,
    execInstr, Function.update_of_ne hi]

abbrev startCmd (p : Ports R S) (success : Fin R) : StructuredCalls.Cmd R S :=
  .seq (clearCmd success) (testCmd p)

noncomputable def startState (p : Ports R S) (success : Fin R)
    (d : Data R S) : Data R S := testResult p (clearState success d)

theorem start_eval (p : Ports R S) (success : Fin R) (d : Data R S)
    (hs : d.stacks p.scratch = []) :
    StructuredCalls.Eval (startCmd p success)
      (8 * (d.stacks p.remaining).length + 8) d (startState p success d) := by
  have h := StructuredCalls.Eval.seq
    (StructuredCalls.Eval.base (StructuredProgram.Eval.atom (.set success false) d))
    (test_eval p (clearState success d) hs)
  rw [clearState_stacks] at h
  unfold startCmd startState clearCmd
  convert h using 1
  omega

theorem startState_stacks (p : Ports R S) (success : Fin R) (d : Data R S)
    (hs : d.stacks p.scratch = []) : (startState p success d).stacks = d.stacks := by
  exact testResult_stacks p (clearState success d) hs

theorem startState_success (p : Ports R S) (success : Fin R)
    (hf : ∀ j, p.register j ≠ success) (d : Data R S) :
    (startState p success d).regs success = false := by
  rw [startState, testResult_other_register p _ success hf, clearState_flag]

theorem startState_guard (p : Ports R S) (success : Fin R) (d : Data R S) :
    (startState p success d).regs (p.register 2) = !(isZero (d.stacks p.remaining)) := by
  rw [startState, testResult_flag, clearState_stacks]

abbrev stopCmd (p : Ports R S) : StructuredCalls.Cmd R S := clearCmd (p.register 2)

def stopState (p : Ports R S) (d : Data R S) : Data R S := clearState (p.register 2) d

@[simp] theorem stopState_stacks (p : Ports R S) (d : Data R S) :
    (stopState p d).stacks = d.stacks := rfl

@[simp] theorem stopState_guard (p : Ports R S) (d : Data R S) :
    (stopState p d).regs (p.register 2) = false := clearState_flag _ _

theorem stopState_success (p : Ports R S) (success : Fin R)
    (hf : ∀ j, p.register j ≠ success) (d : Data R S) :
    (stopState p d).regs success = d.regs success :=
  clearState_other_register _ _ _ (Ne.symm (hf 2))

abbrev loopCmd (p : Ports R S) (success : Fin R) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.Cmd R S :=
  .while (p.register 2) (.seq body (.ite success (stopCmd p) (advanceTestCmd p)))

abbrev search (p : Ports R S) (success : Fin R) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.Cmd R S := .seq (startCmd p success) (loopCmd p success body)

/-- The result is read from the retained current word and the success bit. -/
def result (p : Ports R S) (success : Fin R) (d : Data R S) : Option ℕ :=
  if d.regs success then some (value (d.stacks p.current)) else none

/-- Actual callback entries and their actual instruction counts. -/
inductive Visits (p : Ports R S) (success : Fin R) (body : StructuredCalls.Cmd R S) :
    List ℕ → List ℕ → ℕ → Data R S → Data R S → Prop
  | exhausted (d : Data R S) (hg : d.regs (p.register 2) = false)
      (hf : d.regs success = false) : Visits p success body [] [] 1 d d
  | found {d e : Data R S} {nb : ℕ}
      (hg : d.regs (p.register 2) = true)
      (hb : StructuredCalls.Eval body nb d e)
      (hc : e.stacks p.current = d.stacks p.current)
      (hr : e.stacks p.remaining = d.stacks p.remaining)
      (hs : e.stacks p.scratch = []) (hf : e.regs success = true) :
      Visits p success body [value (d.stacks p.current)] [nb] (nb + 4) d (stopState p e)
  | miss {d e f : Data R S} {nb nt : ℕ} {labels costs : List ℕ}
      (hg : d.regs (p.register 2) = true)
      (hb : StructuredCalls.Eval body nb d e)
      (hc : e.stacks p.current = d.stacks p.current)
      (hr : e.stacks p.remaining = d.stacks p.remaining)
      (hs : e.stacks p.scratch = []) (hf : e.regs success = false)
      (tail : Visits p success body labels costs nt (nextState p e) f) :
      Visits p success body (value (d.stacks p.current) :: labels) (nb :: costs)
        ((nb + advanceTestCost p e + 1) + nt + 1) d f

theorem Visits.eval {p : Ports R S} {success : Fin R}
    {body : StructuredCalls.Cmd R S} {labels costs : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p success body labels costs n d e) :
    StructuredCalls.Eval (loopCmd p success body) n d e := by
  induction h with
  | exhausted d hg hf => exact .while_false hg
  | @found d e nb hg hb hc hr hs hf =>
      have hstop : StructuredCalls.Eval (stopCmd p) 1 e (stopState p e) :=
        .base (.atom (.set (p.register 2) false) e)
      have hstep : StructuredCalls.Eval
          (.seq body (.ite success (stopCmd p) (advanceTestCmd p)))
          (nb + (1 + 1)) d (stopState p e) := .seq hb (.ite_true hf hstop)
      have hdone : StructuredCalls.Eval (loopCmd p success body) 1
          (stopState p e) (stopState p e) := .while_false (stopState_guard p e)
      have h := StructuredCalls.Eval.while_true hg hstep hdone
      simpa only [loopCmd, Nat.add_assoc, Nat.reduceAdd] using h
  | @miss d a e nb nt labels costs hg hb hc hr hs hf ht ih =>
      have h : StructuredCalls.Eval (loopCmd p success body)
          (nb + (advanceTestCost p a + 1) + nt + 1) d e :=
        .while_true hg (.seq hb (.ite_false hf (advanceTest_eval p _ hs))) ih
      simpa only [Nat.add_assoc] using h

theorem Visits.costs_length {p : Ports R S} {success : Fin R}
    {body : StructuredCalls.Cmd R S} {labels costs : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p success body labels costs n d e) : costs.length = labels.length := by
  induction h with
  | exhausted => rfl
  | found => rfl
  | miss hg hb hc hr hs hf ht ih => simpa using ih

/-- Callback payload stacks remain framed during both successful and failed
controller transitions. -/
theorem Visits.stack_preserved {p : Ports R S} {success : Fin R}
    {body : StructuredCalls.Cmd R S} {labels costs : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p success body labels costs n d e)
    (i : Fin S) (hc : i ≠ p.current) (hr : i ≠ p.remaining) (hs : i ≠ p.scratch)
    (hb : ∀ nb a b, StructuredCalls.Eval body nb a b → b.stacks i = a.stacks i) :
    e.stacks i = d.stacks i := by
  induction h with
  | exhausted => rfl
  | @found d a nb hg he hcur hrem hscratch hf => exact hb nb d a he
  | @miss d a e nb nt labels costs hg he hcur hrem hscratch hf ht ih =>
      rw [ih, nextState_other_stack p a i hc hr hs, hb nb d a he]

/-- Costs are the sum of the actual callback counts plus a bound on the
binary controller. No global assumption about callback cost occurs here. -/
theorem Visits.steps_le {p : Ports R S} {success : Fin R}
    {body : StructuredCalls.Cmd R S} {labels costs : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p success body labels costs n d e) (L M : ℕ)
    (hcount : labels.length ≤ value (d.stacks p.remaining))
    (hcurrent : (d.stacks p.current).length + labels.length ≤ L)
    (hremaining : (d.stacks p.remaining).length ≤ M) :
    n ≤ costs.sum + labels.length * (8 * L + 16 * M + 25) + 1 := by
  induction h generalizing L M with
  | exhausted => simp
  | found hg hb hc hr hs hf => simp
  | @miss d a e nb nt labels costs hg hb hc hr hs hf ht ih =>
      have hp : 0 < value (a.stacks p.remaining) := by
        rw [hr]
        simp only [List.length_cons] at hcount
        omega
      have hncount : labels.length ≤ value ((nextState p a).stacks p.remaining) := by
        rw [nextState_remaining, hr]
        have hv := value_decrement hp
        rw [hr] at hv
        simp only [List.length_cons] at hcount
        omega
      have hncurrent : ((nextState p a).stacks p.current).length + labels.length ≤ L := by
        rw [nextState_current, hc]
        have hw := ripple_length_le true (a.stacks p.current)
        rw [hc] at hw
        simp only [List.length_cons] at hcurrent
        omega
      have hnremaining : ((nextState p a).stacks p.remaining).length ≤ M := by
        rw [nextState_remaining, decrement_length hp, hr]
        exact hremaining
      have hit := ih L M hncount hncurrent hnremaining
      have hcost := advanceTestCost_le p a hp
      have hwidth : (a.stacks p.current).length ≤ L := by
        rw [hc]
        simp only [List.length_cons] at hcurrent
        omega
      have hwidth' : (a.stacks p.remaining).length ≤ M := by simpa [hr] using hremaining
      simp only [List.length_cons, List.sum_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- A uniform callback bound is needed only on invariant states actually
visited, and applies to the recorded cost list of those executions. -/
theorem Visits.costs_le_of_invariant {p : Ports R S} {success : Fin R}
    {body : StructuredCalls.Cmd R S} {labels costs : List ℕ} {n : ℕ} {d e : Data R S}
    (h : Visits p success body labels costs n d e)
    (P : Data R S → Prop) (hP : P d) (C : ℕ)
    (hcount : labels.length ≤ value (d.stacks p.remaining))
    (hb : ∀ nb a b, StructuredCalls.Eval body nb a b → P a → P b ∧ nb ≤ C)
    (hn : ∀ a, P a → a.stacks p.scratch = [] →
      0 < value (a.stacks p.remaining) → P (nextState p a)) :
    costs.sum ≤ labels.length * C := by
  induction h with
  | exhausted => simp
  | @found d a nb hg he hc hr hs hf =>
      simpa using (hb nb d a he hP).2
  | @miss d a e nb nt labels costs hg he hc hr hs hf ht ih =>
      obtain ⟨ha, hnb⟩ := hb nb d a he hP
      have hp : 0 < value (a.stacks p.remaining) := by
        rw [hr]
        simp only [List.length_cons] at hcount
        omega
      have hncount : labels.length ≤ value ((nextState p a).stacks p.remaining) := by
        rw [nextState_remaining, hr]
        have hv := value_decrement hp
        rw [hr] at hv
        simp only [List.length_cons] at hcount
        omega
      have hit := ih (hn a ha hs hp) hncount
      simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- A correctness contract supplies concrete body executions only on the
invariant states reached by the client. The executable program has no `test`
or `P` argument. -/
abbrev BodyContract (p : Ports R S) (success : Fin R) (body : StructuredCalls.Cmd R S)
    (test : ℕ → Bool) (P : Data R S → Prop) : Prop :=
  ∀ d, P d → d.stacks p.scratch = [] →
    ∃ nb e, StructuredCalls.Eval body nb d e ∧ P e ∧
      e.stacks p.current = d.stacks p.current ∧
      e.stacks p.remaining = d.stacks p.remaining ∧ e.stacks p.scratch = [] ∧
      e.regs success = test (value (d.stacks p.current))

/-- Exact scan semantics, including the count and order of actual callbacks. -/
theorem visits_exists_guarded (p : Ports R S) (success : Fin R)
    (hf : ∀ j, p.register j ≠ success) (body : StructuredCalls.Cmd R S)
    (test : ℕ → Bool) (P : Data R S → Prop) (hb : BodyContract p success body test P)
    (hn : ∀ d, P d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.remaining) → P (nextState p d)) (fuel : ℕ) :
    ∀ d, P d → value (d.stacks p.remaining) = fuel → d.stacks p.scratch = [] →
      d.regs (p.register 2) = !(isZero (d.stacks p.remaining)) →
      d.regs success = false →
      ∃ labels costs n e, Visits p success body labels costs n d e ∧
        result p success e = (ParameterOrder.scanFrom test (value (d.stacks p.current)) fuel).1 ∧
        labels.length = (ParameterOrder.scanFrom test (value (d.stacks p.current)) fuel).2 ∧
        labels = List.range' (value (d.stacks p.current)) labels.length ∧
        labels.length ≤ fuel ∧ e.stacks p.scratch = [] := by
  induction fuel with
  | zero =>
      intro d hP hv hs hg hfalse
      have hz := (isZero_eq_true_iff _).2 hv
      refine ⟨[], [], 1, d, .exhausted d (by simpa [hz] using hg) hfalse, ?_⟩
      simp [result, hfalse, ParameterOrder.scanFrom, hs]
  | succ fuel ih =>
      intro d hP hv hs hg hfalse
      have hp : 0 < value (d.stacks p.remaining) := by omega
      have hz := (isZero_eq_false_iff _).2 hp
      have hg' : d.regs (p.register 2) = true := by simpa [hz] using hg
      obtain ⟨nb, e, he, hPe, hc, hr, hes, heflag⟩ := hb d hP hs
      cases ht : test (value (d.stacks p.current)) with
      | true =>
          have htrue : e.regs success = true := by simpa [ht] using heflag
          refine ⟨[value (d.stacks p.current)], [nb], nb + 4, stopState p e,
            .found hg' he hc hr hes htrue, ?_⟩
          simp [result, stopState_success p success hf, htrue, hc,
            ParameterOrder.scanFrom, ht, hes, List.range'_succ]
      | false =>
          have hefalse : e.regs success = false := by simpa [ht] using heflag
          have hep : 0 < value (e.stacks p.remaining) := by simpa [hr] using hp
          have hnext : value ((nextState p e).stacks p.remaining) = fuel := by
            rw [nextState_remaining]
            have hv' := value_decrement hep
            have hv'' : value (e.stacks p.remaining) = fuel + 1 := by rw [hr, hv]
            omega
          have hcurrent : value ((nextState p e).stacks p.current) =
              value (d.stacks p.current) + 1 := by
            rw [nextState_current, value_increment, hc]
          obtain ⟨labels, costs, nt, f, hvisits, hresult, hlen, hlabels, hbound, hfs⟩ :=
            ih (nextState p e) (hn e hPe hes hep) hnext (nextState_scratch ..) (nextState_flag ..)
              (by rw [nextState_other_register p e success hf, hefalse])
          rw [hcurrent] at hresult hlen hlabels
          refine ⟨value (d.stacks p.current) :: labels, nb :: costs,
            (nb + advanceTestCost p e + 1) + nt + 1, f,
            .miss hg' he hc hr hes hefalse hvisits, ?_⟩
          refine ⟨?_, ?_, ?_, by simpa using Nat.succ_le_succ hbound, hfs⟩
          · simpa [ParameterOrder.scanFrom, ht] using hresult
          · simpa [ParameterOrder.scanFrom, ht] using congrArg Nat.succ hlen
          · simpa only [List.length_cons, List.range'_succ] using
              congrArg (List.cons (value (d.stacks p.current))) hlabels

/-- Compatibility form for invariants stable under every controller advance. -/
theorem visits_exists (p : Ports R S) (success : Fin R)
    (hf : ∀ j, p.register j ≠ success) (body : StructuredCalls.Cmd R S)
    (test : ℕ → Bool) (P : Data R S → Prop) (hb : BodyContract p success body test P)
    (hn : ∀ d, P d → P (nextState p d)) (fuel : ℕ) :
    ∀ d, P d → value (d.stacks p.remaining) = fuel → d.stacks p.scratch = [] →
      d.regs (p.register 2) = !(isZero (d.stacks p.remaining)) →
      d.regs success = false →
      ∃ labels costs n e, Visits p success body labels costs n d e ∧
        result p success e = (ParameterOrder.scanFrom test (value (d.stacks p.current)) fuel).1 ∧
        labels.length = (ParameterOrder.scanFrom test (value (d.stacks p.current)) fuel).2 ∧
        labels = List.range' (value (d.stacks p.current)) labels.length ∧
        labels.length ≤ fuel ∧ e.stacks p.scratch = [] :=
  visits_exists_guarded p success hf body test P hb (fun d hd _ _ => hn d hd) fuel

/-- The first successful binary label is retained. An exhausted interval
returns `none`, even when the incoming success register is dirty. -/
theorem search_correct (p : Ports R S) (success : Fin R)
    (hf : ∀ j, p.register j ≠ success) (body : StructuredCalls.Cmd R S)
    (test : ℕ → Bool) (P : Data R S → Prop) (hb : BodyContract p success body test P)
    (hn : ∀ d, P d → P (nextState p d)) (d : Data R S)
    (hs : d.stacks p.scratch = []) (hP : P (startState p success d)) :
    ∃ labels costs n e, StructuredCalls.Eval (search p success body) n d e ∧
      (∃ nt, Visits p success body labels costs nt (startState p success d) e) ∧
      result p success e =
        (ParameterOrder.scanFrom test (value (d.stacks p.current))
          (value (d.stacks p.remaining))).1 ∧
      labels.length = (ParameterOrder.scanFrom test (value (d.stacks p.current))
        (value (d.stacks p.remaining))).2 ∧
      labels = List.range' (value (d.stacks p.current)) labels.length ∧
      labels.length ≤ value (d.stacks p.remaining) ∧ e.stacks p.scratch = [] := by
  have hst := startState_stacks p success d hs
  obtain ⟨labels, costs, nt, e, ht, hr, hl, hlabels, hbound, hes⟩ :=
    visits_exists p success hf body test P hb hn (value (d.stacks p.remaining))
      (startState p success d) hP (by rw [hst]) (by rw [hst]; exact hs)
      (by rw [startState_guard, hst]) (startState_success p success hf d)
  refine ⟨labels, costs, (8 * (d.stacks p.remaining).length + 8) + nt, e,
    .seq (start_eval p success d hs) ht.eval, ⟨nt, ht⟩, ?_⟩
  simpa only [hst] using And.intro hr (And.intro hl (And.intro hlabels (And.intro hbound hes)))

/-- A whole-search instruction bound charges the measured callback costs.
The bound therefore remains useful for bodies bounded only on their reachable
invariant states. -/
theorem search_measured (p : Ports R S) (success : Fin R)
    (hf : ∀ j, p.register j ≠ success) (body : StructuredCalls.Cmd R S)
    (test : ℕ → Bool) (P : Data R S → Prop) (hb : BodyContract p success body test P)
    (hn : ∀ d, P d → d.stacks p.scratch = [] →
      0 < value (d.stacks p.remaining) → P (nextState p d)) (d : Data R S)
    (hs : d.stacks p.scratch = []) (hP : P (startState p success d)) :
    ∃ labels costs n e, StructuredCalls.Eval (search p success body) n d e ∧
      (∃ nt, Visits p success body labels costs nt (startState p success d) e ∧
        n = (8 * (d.stacks p.remaining).length + 8) + nt) ∧
      result p success e =
        (ParameterOrder.scanFrom test (value (d.stacks p.current))
          (value (d.stacks p.remaining))).1 ∧
      labels.length = (ParameterOrder.scanFrom test (value (d.stacks p.current))
        (value (d.stacks p.remaining))).2 ∧
      costs.length = labels.length ∧
      n ≤ costs.sum + 8 * (d.stacks p.remaining).length + 9 +
        value (d.stacks p.remaining) *
          (8 * ((d.stacks p.current).length + value (d.stacks p.remaining)) +
            16 * (d.stacks p.remaining).length + 25) ∧
      e.stacks p.scratch = [] := by
  have hst := startState_stacks p success d hs
  obtain ⟨labels, costs, nt, e, ht, hr, hl, hlabels, hbound, hes⟩ :=
    visits_exists_guarded p success hf body test P hb hn (value (d.stacks p.remaining))
      (startState p success d) hP (by rw [hst]) (by rw [hst]; exact hs)
      (by rw [startState_guard, hst]) (startState_success p success hf d)
  have hsteps := ht.steps_le
    ((d.stacks p.current).length + value (d.stacks p.remaining))
    (d.stacks p.remaining).length (by simpa only [hst] using hbound)
    (by rw [hst]; omega) (by rw [hst])
  have hmul := Nat.mul_le_mul_right
    (8 * ((d.stacks p.current).length + value (d.stacks p.remaining)) +
      16 * (d.stacks p.remaining).length + 25) hbound
  refine ⟨labels, costs, (8 * (d.stacks p.remaining).length + 8) + nt, e,
    .seq (start_eval p success d hs) ht.eval, ⟨nt, ht, rfl⟩,
    ?_, ?_, ht.costs_length, ?_, hes⟩
  · simpa only [hst] using hr
  · simpa only [hst] using hl
  · omega

/-- No body execution is needed for an empty input interval, and clearing
the result flag makes its negative outcome independent of incoming registers. -/
theorem search_empty (p : Ports R S) (success : Fin R)
    (hf : ∀ j, p.register j ≠ success) (body : StructuredCalls.Cmd R S)
    (d : Data R S) (hs : d.stacks p.scratch = [])
    (hv : value (d.stacks p.remaining) = 0) :
    StructuredCalls.Eval (search p success body) (8 * (d.stacks p.remaining).length + 9)
      d (startState p success d) ∧ result p success (startState p success d) = none := by
  have hz := (isZero_eq_true_iff _).2 hv
  have hloop : StructuredCalls.Eval (loopCmd p success body) 1
      (startState p success d) (startState p success d) :=
    .while_false (by rw [startState_guard, hz]; rfl)
  refine ⟨?_, ?_⟩
  · simpa only [search, Nat.add_assoc, Nat.reduceAdd] using
      (start_eval p success d hs).seq hloop
  · simp [result, startState_success p success hf]

theorem search_size (p : Ports R S) (success : Fin R) (body : StructuredCalls.Cmd R S) :
    StructuredCalls.size (search p success body) = StructuredCalls.size body + 48 := by
  simp [ StructuredCalls.size, StructuredProgram.size]
  omega

abbrev program (p : Ports R S) (success : Fin R) (body : StructuredCalls.Cmd R S) :=
  StructuredCalls.compiled (search p success body) p.remaining p.current

theorem program_trace (p : Ports R S) (success : Fin R) (body : StructuredCalls.Cmd R S)
    {n : ℕ} {d e : Data R S} (h : StructuredCalls.Eval (search p success body) n d e) :
    Trace (program p success body) (n + 1)
      (d.withPC (some (program p success body).entry)) (e.withPC none) :=
  StructuredCalls.compiled_halt_trace h p.remaining p.current

theorem program_primitive (p : Ports R S) (success : Fin R) (body : StructuredCalls.Cmd R S)
    {n : ℕ} {d e : Data R S} (h : StructuredCalls.Eval (search p success body) n d e) :
    Computation.RunsIn (BitProgram.primitive (program p success body)).step
      (BitProgram.primitiveOverhead (program p success body) * (n + 1))
      (BitProgram.primitiveCfg (program p success body)
        (d.withPC (some (program p success body).entry)))
      (BitProgram.primitiveCfg (program p success body) (e.withPC none)) :=
  StructuredCalls.primitive_execution h p.remaining p.current

end SubexponentialSAT.SubexpFirstSuccessProgram

end OAI.Algorithms
