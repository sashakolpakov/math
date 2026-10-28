import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpPrimeProgram
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-!
# Concrete workspace preparation for a primality trial

The ambient machine has nine Boolean registers and ten Boolean stacks. Stack
5 holds the divisor, stack 7 the loop fuel, stack 8 controller scratch, and
stack 9 a preserved copy of the candidate. Register 8 is the primality flag.

Preparation clears stacks 0--4 and 6, then copies stack 9 to stack 6 through
the empty scratch stack 1. The lifted divisibility routine operates on stacks
0--6. Every operation below is compiled from actual finite bit instructions.
-/

namespace SubexponentialSAT.SubexpPrimeTrialPrep

open BitProgram StructuredProgram StructuredCalls

abbrev State := StructuredProgram.State 9 10

abbrev clearOne (stack : Fin 10) : StructuredCalls.Cmd 9 10 :=
  .call (StackRoutines.clearProgram stack 0 1)

def afterClear (stack : Fin 10) (a : State) : State :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks stack a.stacks⟩

theorem clearOne_eval (stack : Fin 10) (a : State) :
    StructuredCalls.Eval (clearOne stack) (2 * (a.stacks stack).length + 3)
      a (afterClear stack a) :=
  .call _ (ListRegisterProgram.clear_run stack 0 1 a.regs a.stacks)

def clearMany : List (Fin 10) → StructuredCalls.Cmd 9 10
  | [] => .base .skip
  | stack :: rest => .seq (clearOne stack) (clearMany rest)

def afterClearMany : List (Fin 10) → State → State
  | [], a => a
  | stack :: rest, a => afterClearMany rest (afterClear stack a)

def clearManyTime : List (Fin 10) → State → ℕ
  | [], _ => 0
  | stack :: rest, a =>
      2 * (a.stacks stack).length + 3 + clearManyTime rest (afterClear stack a)

theorem clearMany_eval (work : List (Fin 10)) (a : State) :
    StructuredCalls.Eval (clearMany work) (clearManyTime work a) a
      (afterClearMany work a) := by
  induction work generalizing a with
  | nil => exact .base (.skip a)
  | cons stack rest ih => exact (clearOne_eval stack a).seq (ih _)

def workStacks : List (Fin 10) := [0, 1, 2, 3, 4, 6]

abbrev copyOne (source destination scratch : Fin 10) : StructuredCalls.Cmd 9 10 :=
  .call (StackRoutines.copyProgram source destination scratch 0 1)

def afterCopyOne (source destination : Fin 10) (a : State) : State :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks source destination a.stacks⟩

theorem copyOne_eval (source destination scratch : Fin 10) (a : State)
    (hsd : source ≠ destination) (hss : source ≠ scratch) (hsd' : scratch ≠ destination)
    (hscratch : a.stacks scratch = []) :
    StructuredCalls.Eval (copyOne source destination scratch)
      (7 * (a.stacks source).length + 5) a (afterCopyOne source destination a) :=
  .call _ (ListRegisterProgram.copy_run source destination scratch 0 1
    hsd hss hsd' (by decide) a.regs a.stacks hscratch)

abbrev copyCandidate : StructuredCalls.Cmd 9 10 := copyOne 9 6 1

def afterCopy (a : State) : State :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.copyStacks 9 6 a.stacks⟩

theorem copyCandidate_eval (a : State) (hscratch : a.stacks 1 = []) :
    StructuredCalls.Eval copyCandidate (7 * (a.stacks 9).length + 5) a (afterCopy a) :=
  .call _ (ListRegisterProgram.copy_run 9 6 1 0 1 (by decide) (by decide)
    (by decide) (by decide) a.regs a.stacks hscratch)

abbrev prepare : StructuredCalls.Cmd 9 10 :=
  .seq (clearMany workStacks) copyCandidate

/-- The expected division workspace, retaining all controller data. -/
def prepared (a : State) : State :=
  ⟨readRegs a.regs 0 1 none,
    ![[], [], [], [], [], a.stacks 5, a.stacks 9, a.stacks 7, a.stacks 8, a.stacks 9]⟩

def preparationTime (a : State) : ℕ :=
  2 * ((a.stacks 0).length + (a.stacks 1).length + (a.stacks 2).length +
    (a.stacks 3).length + (a.stacks 4).length + (a.stacks 6).length) +
    7 * (a.stacks 9).length + 23

private theorem state_ext {a b : State} (hr : a.regs = b.regs)
    (hs : a.stacks = b.stacks) : a = b := by
  cases a
  cases b
  cases hr
  cases hs
  rfl

theorem afterClearMany_scratch (a : State) :
    (afterClearMany workStacks a).stacks 1 = [] := by
  simp [afterClearMany, workStacks, afterClear, StackRoutines.clearStacks]

theorem afterCopy_clearMany (a : State) :
    afterCopy (afterClearMany workStacks a) = prepared a := by
  apply state_ext
  · simp [afterCopy, afterClearMany, workStacks, afterClear, prepared,
      StackRoutines.readRegs_reset]
  · funext i
    fin_cases i <;>
      simp [afterCopy, afterClearMany, workStacks, afterClear, prepared,
        StackRoutines.clearStacks, StackRoutines.copyStacks]

theorem prepare_eval (a : State) :
    StructuredCalls.Eval prepare (preparationTime a) a (prepared a) := by
  have h := (clearMany_eval workStacks a).seq
    (copyCandidate_eval (afterClearMany workStacks a) (afterClearMany_scratch a))
  rw [afterCopy_clearMany] at h
  have ht : clearManyTime workStacks a +
      (7 * ((afterClearMany workStacks a).stacks 9).length + 5) = preparationTime a := by
    simp [clearManyTime, workStacks, afterClear, afterClearMany, StackRoutines.clearStacks,
      preparationTime]
    omega
  exact ht ▸ h

@[simp] theorem prepared_flag (a : State) : (prepared a).regs 8 = a.regs 8 := by
  simp [prepared, readRegs]

theorem prepared_register_frame (a : State) (i : Fin 9) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    (prepared a).regs i = a.regs i := by simp [prepared, readRegs, hi0, hi1]

theorem prepared_stack_frame (a : State) (i : Fin 10)
    (hi : i = 5 ∨ i = 7 ∨ i = 8 ∨ i = 9) : (prepared a).stacks i = a.stacks i := by
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

def trialStack (i : Fin 7) : Fin 10 := Fin.castAdd 3 i

theorem trialStack_injective : Function.Injective trialStack := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 10 => k.val) h

def trialProgram := StructuredCalls.compiled SubexpPrimeProgram.divisibilityTrial 6 0

abbrev trial : StructuredCalls.Cmd 9 10 :=
  .call (ProgramLinking.liftProgram trialProgram id trialStack)

abbrev prepareAndTrial : StructuredCalls.Cmd 9 10 := .seq prepare trial

/-- Install the seven-stack subroutine state, framing the three controller
stacks. This is a proof-level configuration map, not a machine instruction. -/
noncomputable def install (frame : State) (localState : StructuredProgram.State 9 7) : State :=
  StructuredCalls.embedState id trialStack frame localState

@[simp] theorem install_regs (frame : State) (localState : StructuredProgram.State 9 7) :
    (install frame localState).regs = localState.regs := by
  simp [install, StructuredCalls.embedState]

theorem install_low (frame : State) (localState : StructuredProgram.State 9 7) (i : Fin 7) :
    (install frame localState).stacks (trialStack i) = localState.stacks i :=
  StructuredCalls.embedState_stack id trialStack frame localState trialStack_injective i

theorem install_high (frame : State) (localState : StructuredProgram.State 9 7)
    (i : Fin 10) (hi : 7 ≤ i.val) :
    (install frame localState).stacks i = frame.stacks i := by
  apply StructuredCalls.embedState_stack_frame
  rintro ⟨j, hj⟩
  have hv := congrArg (fun k : Fin 10 => k.val) hj
  change j.val = i.val at hv
  omega

theorem divisionState_regs (regs : Fin 9 → Bool) (result modulus input : List Bool) :
    (SubexpPrimeProgram.divisionState (regs ∘ SubexpPrimeProgram.divisionRegister)
      (regs 8) result modulus input).regs = regs := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact SubexpPrimeProgram.divisionState_flag _ _ _ _ _
  · exact StructuredCalls.embedState_register _ _ _ _
      SubexpPrimeProgram.divisionRegister_injective j

noncomputable def localInitial (a : State) : StructuredProgram.State 9 7 :=
  SubexpPrimeProgram.divisionState
    ((prepared a).regs ∘ SubexpPrimeProgram.divisionRegister)
    (a.regs 8) [] (a.stacks 5) (a.stacks 9)

theorem localInitial_regs (a : State) : (localInitial a).regs = (prepared a).regs := by
  unfold localInitial
  rw [← prepared_flag a]
  exact divisionState_regs _ _ _ _

theorem prepared_eq_install (a : State) : prepared a = install a (localInitial a) := by
  apply state_ext
  · rw [install_regs, localInitial_regs]
  · have hl : ∀ i : Fin 7, (install a (localInitial a)).stacks (trialStack i) =
        ModularDivisionPrograms.resting [] (a.stacks 5) (a.stacks 9) i := by
      intro i
      rw [install_low, localInitial, SubexpPrimeProgram.divisionState_stacks]
    have hh := install_high a (localInitial a)
    funext i
    fin_cases i
    · exact (hl 0).symm
    · exact (hl 1).symm
    · exact (hl 2).symm
    · exact (hl 3).symm
    · exact (hl 4).symm
    · exact (hl 5).symm
    · exact (hl 6).symm
    · exact (hh 7 (by decide)).symm
    · exact (hh 8 (by decide)).symm
    · exact (hh 9 (by decide)).symm

def resultStacks (a : State) : Fin 10 → List Bool :=
  ![ModularArithmetic.reduce (a.stacks 5) (a.stacks 9), [], [], [], [],
    a.stacks 5, [], a.stacks 7, a.stacks 8, a.stacks 9]

theorem install_result_stacks (a : State) (localState : StructuredProgram.State 9 7)
    (hs : localState.stacks = ModularDivisionPrograms.resting
      (ModularArithmetic.reduce (a.stacks 5) (a.stacks 9)) (a.stacks 5) []) :
    (install a localState).stacks = resultStacks a := by
  have hl : ∀ i : Fin 7, (install a localState).stacks (trialStack i) =
      ModularDivisionPrograms.resting
        (ModularArithmetic.reduce (a.stacks 5) (a.stacks 9)) (a.stacks 5) [] i := by
    intro i
    rw [install_low, hs]
  have hh := install_high a localState
  funext i
  fin_cases i
  · exact hl 0
  · exact hl 1
  · exact hl 2
  · exact hl 3
  · exact hl 4
  · exact hl 5
  · exact hl 6
  · exact hh 7 (by decide)
  · exact hh 8 (by decide)
  · exact hh 9 (by decide)

def trialBound (a : State) : ℕ :=
  preparationTime a +
    SubexpPrimeProgram.divisibilityTrialBound (a.stacks 5) (a.stacks 9) + 1

/-- Total finite execution, even for a zero-valued divisor. The numerical
modulo interpretation is refined below under the usual positive-divisor premise. -/
theorem prep_execution (a : State) :
    ∃ steps finalState,
      StructuredCalls.Eval prepareAndTrial steps a finalState ∧
      steps ≤ trialBound a ∧
      finalState.regs 8 =
        (a.regs 8 && !(CounterPrograms.isZero
          (ModularArithmetic.reduce (a.stacks 5) (a.stacks 9)))) ∧
      finalState.stacks = resultStacks a := by
  obtain ⟨steps, localState, heval, htime, hflag, hstacks⟩ :=
    SubexpPrimeProgram.divisibilityTrial_execution
      ((prepared a).regs ∘ SubexpPrimeProgram.divisionRegister)
      (a.regs 8) (a.stacks 5) (a.stacks 9)
  have htrace := StructuredCalls.compiled_halt_trace heval 6 0
  have hcall := StructuredCalls.eval_call_lifted trialProgram id trialStack a
    Function.injective_id trialStack_injective htrace
  change StructuredCalls.Eval trial (steps + 1)
    (install a (localInitial a)) (install a localState) at hcall
  rw [← prepared_eq_install] at hcall
  refine ⟨preparationTime a + (steps + 1), install a localState,
    (prepare_eval a).seq hcall, ?_, ?_, install_result_stacks a localState hstacks⟩
  · unfold trialBound
    omega
  · simpa only [install_regs] using hflag

/-- Numerical correctness for the positive divisors used by the prime loop. -/
theorem prep_correct (a : State) (hm : 0 < BinaryArithmetic.toNat (a.stacks 5)) :
    ∃ steps finalState,
      StructuredCalls.Eval prepareAndTrial steps a finalState ∧
      steps ≤ trialBound a ∧
      (finalState.regs 8 = true ↔ a.regs 8 = true ∧
        BinaryArithmetic.toNat (a.stacks 9) % BinaryArithmetic.toNat (a.stacks 5) ≠ 0) ∧
      finalState.stacks = resultStacks a := by
  obtain ⟨steps, finalState, heval, htime, hflag, hstacks⟩ := prep_execution a
  refine ⟨steps, finalState, heval, htime, ?_, hstacks⟩
  rw [hflag]
  simp only [Bool.and_eq_true, Bool.not_eq_true']
  rw [CounterPrograms.isZero_eq_false_iff, CounterPrograms.value_eq_toNat,
    ModularArithmetic.reduce_correct _ _ hm]
  exact and_congr_right (fun _ => Nat.pos_iff_ne_zero)

/-- Every execution of the concrete body has the same postcondition, not only
the witness chosen by the existence proof. -/
theorem prep_post {a finalState : State} {steps : ℕ}
    (h : StructuredCalls.Eval prepareAndTrial steps a finalState) :
    finalState.regs 8 =
      (a.regs 8 && !(CounterPrograms.isZero
        (ModularArithmetic.reduce (a.stacks 5) (a.stacks 9)))) ∧
    finalState.stacks = resultStacks a := by
  obtain ⟨time, result, heval, _, hflag, hstacks⟩ := prep_execution a
  have heq := SubexpPrimeProgram.eval_result_unique h heval 9 0
  rw [heq]
  exact ⟨hflag, hstacks⟩

theorem prep_correct_post {a finalState : State} {steps : ℕ}
    (h : StructuredCalls.Eval prepareAndTrial steps a finalState)
    (hm : 0 < BinaryArithmetic.toNat (a.stacks 5)) :
    (finalState.regs 8 = true ↔ a.regs 8 = true ∧
      BinaryArithmetic.toNat (a.stacks 9) % BinaryArithmetic.toNat (a.stacks 5) ≠ 0) ∧
    finalState.stacks = resultStacks a := by
  obtain ⟨time, result, heval, _, hflag, hstacks⟩ := prep_correct a hm
  have heq := SubexpPrimeProgram.eval_result_unique h heval 9 0
  rw [heq]
  exact ⟨hflag, hstacks⟩

theorem resultStacks_frame (a : State) (i : Fin 10)
    (hi : i = 5 ∨ i = 7 ∨ i = 8 ∨ i = 9) : resultStacks a i = a.stacks i := by
  rcases hi with rfl | rfl | rfl | rfl <;> rfl

theorem prep_stack_frame {a finalState : State} {steps : ℕ}
    (h : StructuredCalls.Eval prepareAndTrial steps a finalState)
    (i : Fin 10) (hi : i = 5 ∨ i = 7 ∨ i = 8 ∨ i = 9) :
    finalState.stacks i = a.stacks i := by
  rw [(prep_post h).2]
  exact resultStacks_frame a i hi

theorem preparationTime_le (a : State) (bound : ℕ)
    (hbound : ∀ i, (a.stacks i).length ≤ bound) :
    preparationTime a ≤ 19 * bound + 23 := by
  have h0 := hbound 0
  have h1 := hbound 1
  have h2 := hbound 2
  have h3 := hbound 3
  have h4 := hbound 4
  have h6 := hbound 6
  have h9 := hbound 9
  unfold preparationTime
  omega

/-- Polynomial bound in the maximum incoming word length. Clearing arbitrary
dirty work stacks is included in this bound. -/
theorem trialBound_le_uniform (a : State) (bound : ℕ)
    (hbound : ∀ i, (a.stacks i).length ≤ bound) :
    trialBound a ≤ 100 * (2 * bound + 1) ^ 2 + 35 * bound + 32 := by
  have hp := preparationTime_le a bound hbound
  have h5 := hbound 5
  have h9 := hbound 9
  have hpow : ((a.stacks 5).length + (a.stacks 9).length + 1) ^ 2 ≤
      (2 * bound + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  unfold trialBound SubexpPrimeProgram.divisibilityTrialBound
  omega

/-- Actual primitive-tape execution of the composed preparation and trial,
including the compiled command's final halt. -/
theorem prep_primitive_execution (a : State) :
    let program := StructuredCalls.compiled prepareAndTrial 9 0
    ∃ finalState : State,
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * (trialBound a + 1))
        (BitProgram.primitiveCfg program (a.withPC (some program.entry)))
        (BitProgram.primitiveCfg program (finalState.withPC none)) ∧
      finalState.regs 8 =
        (a.regs 8 && !(CounterPrograms.isZero
          (ModularArithmetic.reduce (a.stacks 5) (a.stacks 9)))) ∧
      finalState.stacks = resultStacks a := by
  obtain ⟨steps, result, heval, htime, hflag, hstacks⟩ := prep_execution a
  refine ⟨result, ?_, hflag, hstacks⟩
  exact (StructuredCalls.primitive_execution heval 9 0).mono
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right htime 1))

end SubexponentialSAT.SubexpPrimeTrialPrep

end OAI.Algorithms
