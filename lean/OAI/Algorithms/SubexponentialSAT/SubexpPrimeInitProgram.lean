import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeTrialPrep
import OAI.Algorithms.SubexponentialSAT.SubexpEnumerationProgram

namespace OAI.Algorithms

/-!
# Concrete initialization of trial division

The candidate is preserved on stack 9. A fixed program clears its workspace,
copies the candidate, decrements the copy twice, and writes divisor 2 and a
true primality flag. Execution is total even when the candidate is below 2;
the numerical subtraction specification requires candidate at least 2.
-/

namespace SubexponentialSAT.SubexpPrimeInitProgram

open BitProgram StructuredProgram StructuredCalls
open SubexpPrimeTrialPrep SubexpEnumerationProgram CounterPrograms

abbrev State := StructuredProgram.State 9 10

def ports : SubexpEnumerationProgram.Ports 9 10 where
  register := ⟨SubexpPrimeProgram.zeroRegister, SubexpPrimeProgram.zeroRegister_injective⟩
  current := 5
  remaining := 7
  scratch := 8
  current_ne_remaining := by decide
  current_ne_scratch := by decide
  remaining_ne_scratch := by decide

def work : List (Fin 10) := [1, 5, 7, 8]

def cleared (a : State) : State := afterClearMany work a

def copied (a : State) : State := afterCopyOne 9 7 (cleared a)

noncomputable def borrowed (a : State) : State := rippleResult ports false false (copied a)

noncomputable def borrowedTwice (a : State) : State :=
  rippleResult ports false false (borrowed a)

abbrev finish : StructuredCalls.Cmd 9 10 := .base
  (.seq (.atom (.set 0 true))
    (.seq (.atom (.push 5 0))
      (.seq (.atom (.set 0 false))
        (.seq (.atom (.push 5 0)) (.atom (.set 8 true))))))

def afterFinish (a : State) : State :=
  ⟨Function.update (Function.update a.regs 0 false) 8 true,
    Function.update a.stacks 5 (false :: true :: a.stacks 5)⟩

noncomputable def result (a : State) : State := afterFinish (borrowedTwice a)

abbrev command : StructuredCalls.Cmd 9 10 :=
  .seq (clearMany work) (.seq (copyOne 9 7 1)
    (.seq (rippleCmd ports false false) (.seq (rippleCmd ports false false) finish)))

@[simp] theorem cleared_one (a : State) : (cleared a).stacks 1 = [] := by
  simp [cleared, work, afterClearMany, afterClear, StackRoutines.clearStacks]
@[simp] theorem cleared_five (a : State) : (cleared a).stacks 5 = [] := by
  simp [cleared, work, afterClearMany, afterClear, StackRoutines.clearStacks]
@[simp] theorem cleared_seven (a : State) : (cleared a).stacks 7 = [] := by
  simp [cleared, work, afterClearMany, afterClear, StackRoutines.clearStacks]
@[simp] theorem cleared_eight (a : State) : (cleared a).stacks 8 = [] := by
  simp [cleared, work, afterClearMany, afterClear, StackRoutines.clearStacks]
@[simp] theorem cleared_nine (a : State) : (cleared a).stacks 9 = a.stacks 9 := by
  simp [cleared, work, afterClearMany, afterClear, StackRoutines.clearStacks]

@[simp] theorem copied_one (a : State) : (copied a).stacks 1 = [] := by
  simp [copied, afterCopyOne, StackRoutines.copyStacks]
@[simp] theorem copied_five (a : State) : (copied a).stacks 5 = [] := by
  simp [copied, afterCopyOne, StackRoutines.copyStacks]
@[simp] theorem copied_seven (a : State) : (copied a).stacks 7 = a.stacks 9 := by
  simp [copied, afterCopyOne, StackRoutines.copyStacks]
@[simp] theorem copied_eight (a : State) : (copied a).stacks 8 = [] := by
  simp [copied, afterCopyOne, StackRoutines.copyStacks]

@[simp] theorem borrowed_seven (a : State) :
    (borrowed a).stacks 7 = ripple false (a.stacks 9) := by
  simpa [borrowed, ports, target] using rippleResult_target ports false false (copied a)
@[simp] theorem borrowed_eight (a : State) : (borrowed a).stacks 8 = [] :=
  rippleResult_scratch ports false false (copied a)
@[simp] theorem borrowedTwice_seven (a : State) :
    (borrowedTwice a).stacks 7 = ripple false (ripple false (a.stacks 9)) := by
  simpa [borrowedTwice, ports, target] using rippleResult_target ports false false (borrowed a)
@[simp] theorem borrowedTwice_eight (a : State) : (borrowedTwice a).stacks 8 = [] :=
  rippleResult_scratch ports false false (borrowed a)

theorem finish_eval (a : State) : StructuredCalls.Eval finish 5 a (afterFinish a) := by
  have h := (StructuredProgram.Eval.atom (.set (0 : Fin 9) true) a).seq
    ((StructuredProgram.Eval.atom (.push (5 : Fin 10) 0) _).seq
      ((StructuredProgram.Eval.atom (.set (0 : Fin 9) false) _).seq
        ((StructuredProgram.Eval.atom (.push (5 : Fin 10) 0) _).seq
          (StructuredProgram.Eval.atom (.set (8 : Fin 9) true) _))))
  apply StructuredCalls.Eval.base
  simpa [afterFinish, Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr,
    Function.update_idem] using h

def executionTime (a : State) : ℕ := clearManyTime work a +
  ((7 * (a.stacks 9).length + 5) +
    ((rippleCost false (a.stacks 9) + 1) +
      ((rippleCost false (ripple false (a.stacks 9)) + 1) + 5)))

/-- Unconditional actual execution; no candidate lower bound is needed. -/
theorem initializer_execution (a : State) :
    StructuredCalls.Eval command (executionTime a) a (result a) := by
  have hc := clearMany_eval work a
  have hp := copyOne_eval 9 7 1 (cleared a) (by decide) (by decide) (by decide)
    (cleared_one a)
  have hd := ripple_eval ports false false (copied a) (copied_eight a)
  have he := ripple_eval ports false false (borrowed a) (borrowed_eight a)
  have hf := finish_eval (borrowedTwice a)
  change StructuredCalls.Eval (rippleCmd ports false false)
    (rippleCost false ((copied a).stacks 7) + 1) (copied a) (borrowed a) at hd
  change StructuredCalls.Eval (rippleCmd ports false false)
    (rippleCost false ((borrowed a).stacks 7) + 1) (borrowed a) (borrowedTwice a) at he
  rw [copied_seven] at hd
  rw [borrowed_seven] at he
  rw [cleared_nine] at hp
  simpa only [command, executionTime, result] using hc.seq (hp.seq (hd.seq (he.seq hf)))

@[simp] theorem result_flag (a : State) : (result a).regs 8 = true := by
  simp [result, afterFinish]

@[simp] theorem result_fuel (a : State) :
    (result a).stacks 7 = ripple false (ripple false (a.stacks 9)) := by
  simp [result, afterFinish]

@[simp] theorem result_scratch (a : State) : (result a).stacks 8 = [] := by
  simp [result, afterFinish]

@[simp] theorem result_divisor (a : State) : (result a).stacks 5 = [false, true] := by
  have h₁ : (borrowed a).stacks 5 = [] := by
    rw [borrowed, rippleResult_other ports false false _ 5 (by decide) (by decide)]
    exact copied_five a
  have h₂ : (borrowedTwice a).stacks 5 = [] := by
    rw [borrowedTwice, rippleResult_other ports false false _ 5 (by decide) (by decide)]
    exact h₁
  simp [result, afterFinish, h₂]

@[simp] theorem result_one (a : State) : (result a).stacks 1 = [] := by
  have h₁ : (borrowed a).stacks 1 = [] := by
    rw [borrowed, rippleResult_other ports false false _ 1 (by decide) (by decide)]
    exact copied_one a
  have h₂ : (borrowedTwice a).stacks 1 = [] := by
    rw [borrowedTwice, rippleResult_other ports false false _ 1 (by decide) (by decide)]
    exact h₁
  simp [result, afterFinish, h₂]

theorem result_frame (a : State) (j : Fin 10)
    (h1 : j ≠ 1) (h5 : j ≠ 5) (h7 : j ≠ 7) (h8 : j ≠ 8) :
    (result a).stacks j = a.stacks j := by
  simp only [result, afterFinish, Function.update_of_ne h5]
  rw [borrowedTwice, rippleResult_other ports false false _ j h7 h8,
    borrowed, rippleResult_other ports false false _ j h7 h8]
  simp [copied, afterCopyOne, StackRoutines.copyStacks, cleared, afterClearMany,
    work, afterClear, StackRoutines.clearStacks, h1, h5, h7, h8]

@[simp] theorem result_candidate (a : State) : (result a).stacks 9 = a.stacks 9 :=
  result_frame a 9 (by decide) (by decide) (by decide) (by decide)

def timeBound (a : State) : ℕ :=
  2 * ((a.stacks 1).length + (a.stacks 5).length +
    (a.stacks 7).length + (a.stacks 8).length) + 23 * (a.stacks 9).length + 46

theorem executionTime_le (a : State) : executionTime a ≤ timeBound a := by
  have h₁ := rippleCost_le false (a.stacks 9)
  have h₂ := rippleCost_le false (ripple false (a.stacks 9))
  have hl := ripple_length_le false (a.stacks 9)
  simp only [executionTime, clearManyTime, work, afterClear, StackRoutines.clearStacks]
  simp [timeBound] at *
  omega

/-- The fuel has the intended natural subtraction value when the candidate
is at least two. Exact stack representations and the candidate are preserved. -/
theorem initializer_correct (a : State) (ha : 2 ≤ value (a.stacks 9)) :
    StructuredCalls.Eval command (executionTime a) a (result a) ∧
      executionTime a ≤ timeBound a ∧
      value ((result a).stacks 7) = value (a.stacks 9) - 2 ∧
      (result a).stacks 5 = [false, true] ∧ (result a).regs 8 = true ∧
      (result a).stacks 8 = [] ∧ (result a).stacks 9 = a.stacks 9 := by
  refine ⟨initializer_execution a, executionTime_le a, ?_, result_divisor a,
    result_flag a, result_scratch a, result_candidate a⟩
  rw [result_fuel]
  have h₁ := value_decrement (bs := a.stacks 9) (by omega)
  have hp : 0 < value (ripple false (a.stacks 9)) := by omega
  have h₂ := value_decrement hp
  omega

def program := StructuredCalls.compiled command (9 : Fin 10) 9

theorem program_trace (a : State) :
    Trace program (executionTime a + 1)
      (a.withPC (some program.entry)) ((result a).withPC none) :=
  StructuredCalls.compiled_halt_trace (initializer_execution a) 9 9

theorem program_primitive (a : State) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (timeBound a + 1))
      (BitProgram.primitiveCfg program (a.withPC (some program.entry)))
      (BitProgram.primitiveCfg program ((result a).withPC none)) := by
  exact (StructuredCalls.primitive_execution (initializer_execution a) 9 9).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (executionTime_le a) 1))

end SubexponentialSAT.SubexpPrimeInitProgram

end OAI.Algorithms
