import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeCandidateProgram
import OAI.Algorithms.SubexponentialSAT.SubexpFirstSuccessProgram
import OAI.Algorithms.SubexponentialSAT.SubexpEndpointProgram

namespace OAI.Algorithms

/-!
# A concrete first-prime interval search

The candidate test is the closed binary trial-division program. The first-success
controller stores its candidate and remaining count as binary data, and returns
the first prime in the supplied interval. Endpoint construction below is also an
actual finite program on the encoded exponent.
-/

namespace SubexponentialSAT.SubexpPrimeIntervalProgram

open BitProgram StructuredProgram StructuredCalls
open SubexpEnumerationProgram

abbrev State := StructuredProgram.State 9 12

def ports : SubexpEnumerationProgram.Ports 9 12 where
  register := ⟨SubexpPrimeProgram.zeroRegister, SubexpPrimeProgram.zeroRegister_injective⟩
  current := 9
  remaining := 10
  scratch := 11
  current_ne_remaining := by decide
  current_ne_scratch := by decide
  remaining_ne_scratch := by decide

theorem success_frame (j : Fin 3) : ports.register j ≠ 8 := by
  intro h
  exact SubexpPrimeProgram.flag_not_zeroRegister ⟨j, h⟩

def CandidateInvariant (a : State) : Prop := 2 ≤ CounterPrograms.value (a.stacks 9)

abbrev intervalSearch : StructuredCalls.Cmd 9 12 :=
  SubexpFirstSuccessProgram.search ports 8 SubexpPrimeCandidateProgram.candidateTest

def searchResult (a : State) : Option ℕ := SubexpFirstSuccessProgram.result ports 8 a

theorem candidate_contract : SubexpFirstSuccessProgram.BodyContract ports 8
    SubexpPrimeCandidateProgram.candidateTest SubexpPackingParameters.primeTest
    CandidateInvariant := by
  intro a ha hs
  obtain ⟨n, b, he, hp, hc, hr, hsc, hi⟩ :=
    SubexpPrimeCandidateProgram.candidateTest_correct a ha
  refine ⟨n, b, he, ?_, hc, hr, hsc.trans hs, ?_⟩
  · change 2 ≤ CounterPrograms.value (b.stacks 9)
    rw [hc]
    exact ha
  · apply Bool.eq_iff_iff.mpr
    change b.regs 8 = true ↔ decide (Nat.Prime (CounterPrograms.value (a.stacks 9))) = true
    exact hp.trans (Iff.of_eq decide_eq_true_eq.symm)

theorem candidate_next {a : State} (ha : CandidateInvariant a) :
    CandidateInvariant (nextState ports a) := by
  change 2 ≤ CounterPrograms.value ((nextState ports a).stacks ports.current)
  rw [nextState_current, CounterPrograms.value_increment]
  change 2 ≤ CounterPrograms.value (a.stacks 9) + 1
  exact ha.trans (Nat.le_add_right _ _)

/-- No abstract callback hypothesis remains: each visited candidate invokes
the closed binary primality program. The result is exactly the first prime. -/
theorem intervalSearch_correct (a : State) (hs : a.stacks 11 = [])
    (hstart : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    ∃ (labels costs : List ℕ) (n : ℕ) (b : State),
      StructuredCalls.Eval intervalSearch n a b ∧
      (∃ nt, SubexpFirstSuccessProgram.Visits ports 8
        SubexpPrimeCandidateProgram.candidateTest labels costs nt
        (SubexpFirstSuccessProgram.startState ports 8 a) b) ∧
      searchResult b = (ParameterOrder.scanFrom SubexpPackingParameters.primeTest
        (CounterPrograms.value (a.stacks 9)) (CounterPrograms.value (a.stacks 10))).1 ∧
      labels.length = (ParameterOrder.scanFrom SubexpPackingParameters.primeTest
        (CounterPrograms.value (a.stacks 9)) (CounterPrograms.value (a.stacks 10))).2 ∧
      labels = List.range' (CounterPrograms.value (a.stacks 9)) labels.length ∧
      labels.length ≤ CounterPrograms.value (a.stacks 10) ∧ b.stacks 11 = [] := by
  apply SubexpFirstSuccessProgram.search_correct ports 8 success_frame
    SubexpPrimeCandidateProgram.candidateTest SubexpPackingParameters.primeTest
    CandidateInvariant candidate_contract (fun _ h => candidate_next h) a hs
  change 2 ≤ CounterPrograms.value
    ((SubexpFirstSuccessProgram.startState ports 8 a).stacks 9)
  rw [SubexpFirstSuccessProgram.startState_stacks ports 8 a hs]
  exact hstart

def intervalProgram := StructuredCalls.compiled intervalSearch 9 9

theorem intervalSearch_trace (a : State) (hs : a.stacks 11 = [])
    (hstart : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    ∃ (n : ℕ) (b : State), BitProgram.Trace intervalProgram (n + 1)
      (a.withPC (some intervalProgram.entry)) (b.withPC none) ∧
      searchResult b = (ParameterOrder.scanFrom SubexpPackingParameters.primeTest
        (CounterPrograms.value (a.stacks 9)) (CounterPrograms.value (a.stacks 10))).1 := by
  obtain ⟨labels, costs, n, b, he, hv, hr, hl, hlabels, hcount, hs⟩ :=
    intervalSearch_correct a hs hstart
  exact ⟨n, b, StructuredCalls.compiled_halt_trace he 9 9, hr⟩

/-- Fixed endpoint ports: exponent 0, scratch 1, lower 2, start 9,
remaining count 10, upper 3. -/
def endpointStack : Fin 6 → Fin 12 := ![0, 1, 2, 9, 10, 3]

theorem endpointStack_injective : Function.Injective endpointStack := by decide

abbrev endpointCommand : StructuredCalls.Cmd 9 12 :=
  .call (ProgramLinking.liftProgram SubexpEndpointProgram.program
    SubexpPrimeProgram.zeroRegister endpointStack)

def inputState (exponent : List Bool) : State := StructuredProgram.ioState 0 exponent

private theorem extend_restrict_eq {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ h => congrArg g h) g a
  · exact Function.extend_apply' _ _ _ h

theorem endpoint_initial (exponent : List Bool) :
    StructuredCalls.embedState SubexpPrimeProgram.zeroRegister endpointStack
      (inputState exponent) (SubexpEndpointProgram.inputState (fun _ => false) exponent) =
      inputState exponent := by
  apply SubexpEnumerationProgram.data_ext
  · change Function.extend SubexpPrimeProgram.zeroRegister (fun _ => false)
      (fun _ => false) = (fun _ => false)
    exact extend_restrict_eq SubexpPrimeProgram.zeroRegister (fun _ => false)
  · change Function.extend endpointStack
      (SubexpEndpointProgram.inputState (fun _ => false) exponent).stacks
      (inputState exponent).stacks = (inputState exponent).stacks
    have h : (SubexpEndpointProgram.inputState (fun _ => false) exponent).stacks =
        (inputState exponent).stacks ∘ endpointStack := by
      funext i
      fin_cases i <;> rfl
    rw [h, extend_restrict_eq]

theorem endpointCommand_correct (exponent : List Bool) :
    ∃ n b, StructuredCalls.Eval endpointCommand n (inputState exponent) b ∧
      n ≤ SubexpEndpointProgram.runtimeBound exponent ∧
      CounterPrograms.value (b.stacks 9) = 2 ^ CounterPrograms.value exponent + 1 ∧
      CounterPrograms.value (b.stacks 10) = 2 ^ CounterPrograms.value exponent - 1 ∧
      b.stacks 11 = [] := by
  obtain ⟨n, d, hn, hd, he⟩ := SubexpEndpointProgram.lifted_output
    SubexpPrimeProgram.zeroRegister endpointStack SubexpPrimeProgram.zeroRegister_injective
    endpointStack_injective (inputState exponent) (fun _ => false) exponent
  rw [endpoint_initial] at he
  have hv := SubexpEndpointProgram.output_values exponent d hd
  let b := StructuredCalls.embedState SubexpPrimeProgram.zeroRegister endpointStack
    (inputState exponent) d
  refine ⟨n, b, he, hn, ?_, ?_, ?_⟩
  · have h := StructuredCalls.embedState_stack SubexpPrimeProgram.zeroRegister
      endpointStack (inputState exponent) d endpointStack_injective 3
    change b.stacks 9 = d.stacks 3 at h
    rw [h]
    exact hv.2.1
  · have h := StructuredCalls.embedState_stack SubexpPrimeProgram.zeroRegister
      endpointStack (inputState exponent) d endpointStack_injective 4
    change b.stacks 10 = d.stacks 4 at h
    rw [h]
    exact hv.2.2.1
  · have h := StructuredCalls.embedState_stack_frame SubexpPrimeProgram.zeroRegister
      endpointStack (inputState exponent) d 11 (by decide)
    exact h

abbrev exponentSearch : StructuredCalls.Cmd 9 12 := .seq endpointCommand intervalSearch

/-- On an encoded exponent, the program computes the same strict dyadic
interval scan used by the packing schedule. -/
theorem exponentSearch_correct (exponent : List Bool) :
    ∃ n b, StructuredCalls.Eval exponentSearch n (inputState exponent) b ∧
      searchResult b = (ParameterOrder.scanFrom SubexpPackingParameters.primeTest
        (2 ^ CounterPrograms.value exponent + 1) (2 ^ CounterPrograms.value exponent - 1)).1 := by
  obtain ⟨ne, a, he, ht, hc, hr, hs⟩ := endpointCommand_correct exponent
  have hlo : 2 ≤ CounterPrograms.value (a.stacks 9) := by
    rw [hc]
    have hp := Nat.one_le_pow (CounterPrograms.value exponent) 2 (by decide : 0 < (2 : ℕ))
    omega
  obtain ⟨labels, costs, ns, b, hscan, hv, hout, hlen, hl, hcount, hscr⟩ :=
    intervalSearch_correct a hs hlo
  refine ⟨ne + ns, b, he.seq hscan, ?_⟩
  simpa only [hc, hr] using hout

abbrev defaultState (a : State) : State :=
  ⟨Function.update (BitProgram.readRegs a.regs 0 1 none) 0 true,
    Function.update a.stacks 9 [true, true]⟩

/-- Write the schedule's explicit fallback value using a clear loop and
three bit instructions. -/
abbrev writeDefault : StructuredCalls.Cmd 9 12 :=
  .seq (.call (StackRoutines.clearProgram 9 0 1))
    (.base (.seq (.atom (.set 0 true))
      (.seq (.atom (.push 9 0)) (.atom (.push 9 0)))))

theorem writeDefault_eval (a : State) :
    StructuredCalls.Eval writeDefault (2 * (a.stacks 9).length + 6) a (defaultState a) := by
  let z : State := ⟨BitProgram.readRegs a.regs 0 1 none,
    StackRoutines.clearStacks 9 a.stacks⟩
  have hc : StructuredCalls.Eval (.call (StackRoutines.clearProgram 9 0 1))
      (2 * (a.stacks 9).length + 3) a z :=
    .call _ (ListRegisterProgram.clear_run 9 0 1 a.regs a.stacks)
  have hw := (StructuredProgram.Eval.atom (.set (0 : Fin 9) true) z).seq
    ((StructuredProgram.Eval.atom (.push (9 : Fin 12) 0) _).seq
      (StructuredProgram.Eval.atom (.push (9 : Fin 12) 0) _))
  have hw' : StructuredCalls.Eval (.base (.seq (.atom (.set 0 true))
      (.seq (.atom (.push 9 0)) (.atom (.push 9 0))))) 3 z (defaultState a) := by
    apply StructuredCalls.Eval.base
    simpa [defaultState, z, Atom.eval, Atom.instr, State.ofCfg, State.withPC,
      BitProgram.execInstr, StackRoutines.clearStacks, Function.update_idem] using hw
  convert hc.seq hw' using 1

abbrev finishSelection : StructuredCalls.Cmd 9 12 :=
  .ite 8 (.base .skip) writeDefault

theorem finishSelection_correct (a : State) :
    ∃ n b, StructuredCalls.Eval finishSelection n a b ∧
      CounterPrograms.value (b.stacks 9) = (searchResult a).getD 3 := by
  cases hf : a.regs 8 with
  | false =>
      refine ⟨2 * (a.stacks 9).length + 6 + 1, defaultState a,
        .ite_false hf (writeDefault_eval a), ?_⟩
      simp [ searchResult, SubexpFirstSuccessProgram.result, hf,
        CounterPrograms.value]
  | true =>
      refine ⟨1, a, .ite_true hf (.base (.skip a)), ?_⟩
      simp [searchResult, SubexpFirstSuccessProgram.result, hf, ports]

abbrev primeSelectCmd : StructuredCalls.Cmd 9 12 := .seq exponentSearch finishSelection

def selectedPrime (exponent : ℕ) : ℕ :=
  (ParameterOrder.scanFrom SubexpPackingParameters.primeTest
    (2 ^ exponent + 1) (2 ^ exponent - 1)).1.getD 3

theorem primeSelect_correct (exponent : List Bool) :
    ∃ n b, StructuredCalls.Eval primeSelectCmd n (inputState exponent) b ∧
      CounterPrograms.value (b.stacks 9) = selectedPrime (CounterPrograms.value exponent) := by
  obtain ⟨ne, a, he, hr⟩ := exponentSearch_correct exponent
  obtain ⟨nf, b, hf, hv⟩ := finishSelection_correct a
  refine ⟨ne + nf, b, he.seq hf, ?_⟩
  simpa only [hr, selectedPrime] using hv

theorem selectedPrime_eq_schedule (n : ℕ) :
    selectedPrime (SubexpPackingParameters.u n) = SubexpPackingParameters.p n := by
  by_cases hn : SubexpPackingParameters.GoodInput n
  · simp only [selectedPrime, SubexpPackingParameters.p, hn, ite_true,
      SubexpPackingParameters.primeScan]
  · have hu : SubexpPackingParameters.u n ≤ 1 := by
      unfold SubexpPackingParameters.GoodInput at hn
      unfold SubexpPackingParameters.u
      omega
    have hp3 : SubexpPackingParameters.primeTest 3 = true := by decide
    have hcases : SubexpPackingParameters.u n = 0 ∨ SubexpPackingParameters.u n = 1 := by omega
    rcases hcases with hz | ho
    · simp [selectedPrime, hz, SubexpPackingParameters.p, hn, ParameterOrder.scanFrom]
    · simp [selectedPrime, ho, SubexpPackingParameters.p, hn, ParameterOrder.scanFrom, hp3]

/-- The actual program computes the schedule's total prime-selection value
from a binary encoding of its exponent, including the small-input fallback. -/
theorem primeSelect_schedule (n : ℕ) (exponent : List Bool)
    (hexponent : CounterPrograms.value exponent = SubexpPackingParameters.u n) :
    ∃ steps b, StructuredCalls.Eval primeSelectCmd steps (inputState exponent) b ∧
      CounterPrograms.value (b.stacks 9) = SubexpPackingParameters.p n := by
  obtain ⟨steps, b, he, hp⟩ := primeSelect_correct exponent
  exact ⟨steps, b, he, hp.trans (by rw [hexponent, selectedPrime_eq_schedule])⟩

def primeSelectProgram := StructuredCalls.compiled primeSelectCmd 0 9

theorem primeSelect_schedule_trace (n : ℕ) (exponent : List Bool)
    (hexponent : CounterPrograms.value exponent = SubexpPackingParameters.u n) :
    ∃ (steps : ℕ) (b : State), BitProgram.Trace primeSelectProgram (steps + 1)
      ((inputState exponent).withPC (some primeSelectProgram.entry)) (b.withPC none) ∧
      CounterPrograms.value (b.stacks 9) = SubexpPackingParameters.p n := by
  obtain ⟨steps, b, he, hp⟩ := primeSelect_schedule n exponent hexponent
  exact ⟨steps, b, StructuredCalls.compiled_halt_trace he 0 9, hp⟩

theorem primeSelect_schedule_primitive (n : ℕ) (exponent : List Bool)
    (hexponent : CounterPrograms.value exponent = SubexpPackingParameters.u n) :
    ∃ (steps : ℕ) (b : State),
      Computation.RunsIn (BitProgram.primitive primeSelectProgram).step
        (BitProgram.primitiveOverhead primeSelectProgram * (steps + 1))
        (BitProgram.primitiveCfg primeSelectProgram
          ((inputState exponent).withPC (some primeSelectProgram.entry)))
        (BitProgram.primitiveCfg primeSelectProgram (b.withPC none)) ∧
      CounterPrograms.value (b.stacks 9) = SubexpPackingParameters.p n := by
  obtain ⟨steps, b, he, hp⟩ := primeSelect_schedule n exponent hexponent
  exact ⟨steps, b, StructuredCalls.primitive_execution he 0 9, hp⟩

end SubexponentialSAT.SubexpPrimeIntervalProgram

end OAI.Algorithms
