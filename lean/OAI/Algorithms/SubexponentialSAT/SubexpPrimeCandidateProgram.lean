import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeSearchProgram

namespace OAI.Algorithms

/-!
# Calling the primality test inside the candidate search

The inner test uses nine Boolean registers and ten stacks. The outer search
adds two stacks for its remaining count and scratch. The wrapper assigns the
inner stacks to the first ten positions and preserves the outer two positions.
The candidate remains on stack 9 and the test result is register 8.
-/

namespace SubexponentialSAT.SubexpPrimeCandidateProgram

open BitProgram StructuredProgram StructuredCalls

abbrev State := StructuredProgram.State 9 12
abbrev InnerState := StructuredProgram.State 9 10

def stackMap (i : Fin 10) : Fin 12 := Fin.castAdd 2 i

theorem stackMap_injective : Function.Injective stackMap := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 12 => k.val) h

def localState (a : State) : InnerState :=
  ⟨a.regs, a.stacks ∘ stackMap⟩

noncomputable def install (frame : State) (inner : InnerState) : State :=
  StructuredCalls.embedState id stackMap frame inner

@[simp] theorem install_regs (frame : State) (inner : InnerState) :
    (install frame inner).regs = inner.regs := by
  simp [install, StructuredCalls.embedState]

theorem install_low (frame : State) (inner : InnerState) (i : Fin 10) :
    (install frame inner).stacks (stackMap i) = inner.stacks i :=
  StructuredCalls.embedState_stack id stackMap frame inner stackMap_injective i

theorem install_high (frame : State) (inner : InnerState) (i : Fin 12)
    (hi : 10 ≤ i.val) : (install frame inner).stacks i = frame.stacks i := by
  apply StructuredCalls.embedState_stack_frame
  rintro ⟨j, hj⟩
  have hv := congrArg (fun k : Fin 12 => k.val) hj
  change j.val = i.val at hv
  omega

theorem install_local (a : State) : install a (localState a) = a := by
  cases a with
  | mk regs words =>
      apply congrArg₂ StructuredProgram.State.mk
      · simp [ localState ]
      · change Function.extend stackMap (words ∘ stackMap) words = words
        funext i
        by_cases hi : ∃ j, stackMap j = i
        · obtain ⟨j, rfl⟩ := hi
          exact stackMap_injective.extend_apply _ _ j
        · exact Function.extend_apply' _ _ _ hi

abbrev callInner {labels : ℕ} (program : Program 9 10 labels) : StructuredCalls.Cmd 9 12 :=
  .call (ProgramLinking.liftProgram program id stackMap)

/-- Actual subroutine traces lift with exactly the same source-step count. -/
theorem callInner_eval {labels steps : ℕ} (program : Program 9 10 labels)
    (a : State) (b : InnerState)
    (h : BitProgram.Trace program steps
      ((localState a).withPC (some program.entry)) (b.withPC none)) :
    StructuredCalls.Eval (callInner program) steps a (install a b) := by
  have hl := StructuredCalls.eval_call_lifted program id stackMap a
    Function.injective_id stackMap_injective h
  change StructuredCalls.Eval (callInner program) steps
    (install a (localState a)) (install a b) at hl
  simpa only [install_local] using hl

/-- This is the fixed compiled primality test, with two additional framed
stacks for the outer first-success controller. -/
abbrev candidateTest : StructuredCalls.Cmd 9 12 :=
  callInner SubexpPrimeSearchProgram.primeTestProgram

theorem candidateTest_refinement {steps : ℕ} (a : State) (b : InnerState)
    (h : StructuredCalls.Eval SubexpPrimeSearchProgram.primeTestCmd steps
      (localState a) b) :
    StructuredCalls.Eval candidateTest (steps + 1) a (install a b) :=
  callInner_eval _ a b (StructuredCalls.compiled_halt_trace h 9 9)

/-- Total execution of a closed primality test. The original candidate and
both outer controller stacks survive the invocation exactly. -/
theorem candidateTest_execution (a : State) :
    ∃ steps b, StructuredCalls.Eval candidateTest steps a b ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 10 = a.stacks 10 ∧
      b.stacks 11 = a.stacks 11 ∧ b.stacks 8 = [] := by
  obtain ⟨steps, b, heval, hcandidate, hscratch⟩ :=
    SubexpPrimeSearchProgram.primeTest_execution (localState a)
  refine ⟨steps + 1, install a b, candidateTest_refinement a b heval, ?_,
    install_high a b 10 (by decide), install_high a b 11 (by decide), ?_⟩
  · exact (install_low a b 9).trans hcandidate
  · exact (install_low a b 8).trans hscratch

/-- Numeric correctness on the candidate interval used by prime search. -/
theorem candidateTest_correct (a : State)
    (hcandidate : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    ∃ steps b, StructuredCalls.Eval candidateTest steps a b ∧
      (b.regs 8 = true ↔ Nat.Prime (CounterPrograms.value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 10 = a.stacks 10 ∧
      b.stacks 11 = a.stacks 11 ∧ b.stacks 8 = [] := by
  obtain ⟨steps, b, heval, hprime, hcandidate', hscratch⟩ :=
    SubexpPrimeSearchProgram.primeTest_correct (localState a) hcandidate
  refine ⟨steps + 1, install a b, candidateTest_refinement a b heval, ?_, ?_,
    install_high a b 10 (by decide), install_high a b 11 (by decide), ?_⟩
  · change (b.regs 8 = true ↔ Nat.Prime (CounterPrograms.value (a.stacks 9))) at hprime
    simpa only [install_regs] using hprime
  · exact (install_low a b 9).trans hcandidate'
  · exact (install_low a b 8).trans hscratch

theorem candidateTest_frame {steps : ℕ} {a b : State}
    (h : StructuredCalls.Eval candidateTest steps a b) :
    b.stacks 9 = a.stacks 9 ∧ b.stacks 10 = a.stacks 10 ∧
      b.stacks 11 = a.stacks 11 ∧ b.stacks 8 = [] := by
  obtain ⟨time, result, heval, hf⟩ := candidateTest_execution a
  rw [SubexpPrimeProgram.eval_result_unique h heval 9 9]
  exact hf

theorem candidateTest_post {steps : ℕ} {a b : State}
    (h : StructuredCalls.Eval candidateTest steps a b)
    (hcandidate : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    (b.regs 8 = true ↔ Nat.Prime (CounterPrograms.value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 10 = a.stacks 10 ∧
      b.stacks 11 = a.stacks 11 ∧ b.stacks 8 = [] := by
  obtain ⟨time, result, heval, hp⟩ := candidateTest_correct a hcandidate
  rw [SubexpPrimeProgram.eval_result_unique h heval 9 9]
  exact hp

def candidateProgram := StructuredCalls.compiled candidateTest 9 9

/-- Source-level trace of the fully closed candidate body. -/
theorem candidateTest_trace (a : State)
    (hcandidate : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    ∃ (steps : ℕ) (b : State), BitProgram.Trace candidateProgram (steps + 1)
      (a.withPC (some candidateProgram.entry)) (b.withPC none) ∧
      (b.regs 8 = true ↔ Nat.Prime (CounterPrograms.value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 10 = a.stacks 10 ∧
      b.stacks 11 = a.stacks 11 := by
  obtain ⟨steps, b, heval, hp, hcan, hfuel, hscratch, _⟩ := candidateTest_correct a hcandidate
  exact ⟨steps, b, StructuredCalls.compiled_halt_trace heval 9 9,
    hp, hcan, hfuel, hscratch⟩

/-- Compiler-derived primitive execution; no polynomial or asymptotic
prime-search bound is asserted by this existential step-count theorem. -/
theorem candidateTest_primitive_execution (a : State)
    (hcandidate : 2 ≤ CounterPrograms.value (a.stacks 9)) :
    ∃ (steps : ℕ) (b : State),
      Computation.RunsIn (BitProgram.primitive candidateProgram).step
        (BitProgram.primitiveOverhead candidateProgram * (steps + 1))
        (BitProgram.primitiveCfg candidateProgram (a.withPC (some candidateProgram.entry)))
        (BitProgram.primitiveCfg candidateProgram (b.withPC none)) ∧
      (b.regs 8 = true ↔ Nat.Prime (CounterPrograms.value (a.stacks 9))) ∧
      b.stacks 9 = a.stacks 9 ∧ b.stacks 10 = a.stacks 10 ∧
      b.stacks 11 = a.stacks 11 := by
  obtain ⟨steps, b, heval, hp, hcan, hfuel, hscratch, _⟩ := candidateTest_correct a hcandidate
  exact ⟨steps, b, StructuredCalls.primitive_execution heval 9 9,
    hp, hcan, hfuel, hscratch⟩

end SubexponentialSAT.SubexpPrimeCandidateProgram

end OAI.Algorithms
