import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticTestProgram
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticMachine

namespace OAI.Algorithms

/-!
# Fixed scalar scripts for the quartic divisor tests

The scripts preserve all input words. Their temporary words may initially
contain arbitrary data. The modulus and minus-one word are runtime inputs.
-/

namespace SubexponentialSAT.SubexpQuarticDivisorMachine

open SubexponentialSAT.SubexpQuarticMachine SubexponentialSAT.SubexpQuarticTestProgram
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

/-- Inputs: coefficients 0--3, divisor constant 4, minus one 5.
The remainder is written to word 8. -/
def linearScript : List (Instr 9) :=
  [⟨.mul, 6, 4, 5⟩,
   ⟨.add, 7, 3, 6⟩,
   ⟨.mul, 7, 6, 7⟩,
   ⟨.add, 7, 2, 7⟩,
   ⟨.mul, 7, 6, 7⟩,
   ⟨.add, 7, 1, 7⟩,
   ⟨.mul, 7, 6, 7⟩,
   ⟨.add, 8, 0, 7⟩]

/-- Inputs: coefficients 0--3, divisor constants 4--5, minus one 6.
The two remainder coefficients are written to words 12--13. -/
def quadraticScript : List (Instr 14) :=
  [⟨.mul, 7, 4, 6⟩,
   ⟨.mul, 8, 5, 6⟩,
   ⟨.add, 9, 3, 8⟩,
   ⟨.mul, 11, 8, 9⟩,
   ⟨.add, 10, 2, 7⟩,
   ⟨.add, 10, 10, 11⟩,
   ⟨.mul, 12, 7, 10⟩,
   ⟨.add, 12, 0, 12⟩,
   ⟨.mul, 11, 8, 10⟩,
   ⟨.mul, 13, 7, 9⟩,
   ⟨.add, 13, 11, 13⟩,
   ⟨.add, 13, 1, 13⟩]

@[simp] theorem linearScript_length : linearScript.length = 8 := rfl
@[simp] theorem quadraticScript_length : quadraticScript.length = 12 := rfl

def linearPorts : CounterForPrograms.Ports 8 18 :=
  firstPorts (bankPort (8 : Fin 9)) (tempPort 9) (by simp)

abbrev linearTail : StructuredCalls.Cmd 8 18 := CounterForPrograms.testCmd linearPorts

abbrev quadraticTail : StructuredCalls.Cmd 8 23 :=
  pairTestCmd (bankPort (12 : Fin 14)) (bankPort (13 : Fin 14)) (tempPort 14)
    (by simp) (by simp)

noncomputable def linearTailResult (d : StructuredCalls.State 8 18) :
    StructuredCalls.State 8 18 := CounterForPrograms.testResult linearPorts d

noncomputable def quadraticTailResult (d : StructuredCalls.State 8 23) :
    StructuredCalls.State 8 23 :=
  pairTestResult (bankPort (12 : Fin 14)) (bankPort (13 : Fin 14)) (tempPort 14)
    (by simp) (by simp) d

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem linearScript_result (bank : Fin 9 → Word (baseWidth p μ)) :
    scriptEval p μ M linearScript bank 8 =
      linearWord p μ M (bank 5) ![bank 0, bank 1, bank 2, bank 3] (bank 4) := by
  rfl

theorem quadraticScript_result (bank : Fin 14 → Word (baseWidth p μ)) :
    ![scriptEval p μ M quadraticScript bank 12,
      scriptEval p μ M quadraticScript bank 13] =
      quadraticWord p μ M (bank 6) ![bank 0, bank 1, bank 2, bank 3]
        ![bank 4, bank 5] := by
  rfl

theorem linearScript_preserves (bank : Fin 9 → Word (baseWidth p μ)) (i : Fin 6) :
    scriptEval p μ M linearScript bank (Fin.castAdd 3 i) = bank (Fin.castAdd 3 i) := by
  fin_cases i <;> rfl

theorem quadraticScript_preserves (bank : Fin 14 → Word (baseWidth p μ)) (i : Fin 7) :
    scriptEval p μ M quadraticScript bank (Fin.castAdd 7 i) = bank (Fin.castAdd 7 i) := by
  fin_cases i <;> rfl

theorem linearScript_value (bank : Fin 9 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 5) = -1) :
    wordValue p μ (scriptEval p μ M linearScript bank 8) =
      QuarticSearch.linearRemainder
        ![wordValue p μ (bank 0), wordValue p μ (bank 1),
          wordValue p μ (bank 2), wordValue p μ (bank 3)] (wordValue p μ (bank 4)) := by
  rw [linearScript_result]
  exact linearWord_value p μ M _ _ _ hminus

theorem quadraticScript_value (bank : Fin 14 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 6) = -1) (i : Fin 2) :
    wordValue p μ (![scriptEval p μ M quadraticScript bank 12,
      scriptEval p μ M quadraticScript bank 13] i) =
      QuarticSearch.quadraticRemainder
        ![wordValue p μ (bank 0), wordValue p μ (bank 1),
          wordValue p μ (bank 2), wordValue p μ (bank 3)]
        ![wordValue p μ (bank 4), wordValue p μ (bank 5)] i := by
  rw [quadraticScript_result]
  exact quadraticWord_value p μ M _ _ _ hminus i

omit [Fact p.Prime] in
theorem linearTail_eval (regs : Fin 8 → Bool) (bank : Fin 9 → Word (baseWidth p μ)) :
    StructuredCalls.Eval linearTail (8 * baseWidth p μ + 7)
      (restingState regs bank M.bits) (linearTailResult (restingState regs bank M.bits)) := by
  have h := CounterForPrograms.test_eval linearPorts (restingState regs bank M.bits)
    (by simp [linearPorts, firstPorts, restingState])
  simpa [linearTail, linearTailResult, linearPorts, firstPorts, restingState,
    (bank 8).property] using h

omit [Fact p.Prime] in
theorem quadraticTail_eval (regs : Fin 8 → Bool) (bank : Fin 14 → Word (baseWidth p μ)) :
    StructuredCalls.Eval quadraticTail (16 * baseWidth p μ + 15)
      (restingState regs bank M.bits) (quadraticTailResult (restingState regs bank M.bits)) := by
  have h := pairTest_eval (bankPort (12 : Fin 14)) (bankPort (13 : Fin 14)) (tempPort 14)
    (by simp) (by simp) (restingState regs bank M.bits) (by simp [restingState])
  simp only [restingState, store_bank, (bank 12).property, (bank 13).property] at h
  convert h using 1
  all_goals first | rfl | omega

omit [Fact p.Prime] in
theorem linearTail_stacks (regs : Fin 8 → Bool) (bank : Fin 9 → Word (baseWidth p μ)) :
    (linearTailResult (restingState regs bank M.bits)).stacks =
      (restingState regs bank M.bits).stacks := by
  exact CounterForPrograms.testResult_stacks linearPorts _
    (by simp [linearPorts, firstPorts, restingState])

omit [Fact p.Prime] in
theorem quadraticTail_stacks (regs : Fin 8 → Bool) (bank : Fin 14 → Word (baseWidth p μ)) :
    (quadraticTailResult (restingState regs bank M.bits)).stacks =
      (restingState regs bank M.bits).stacks := by
  exact pairTest_stacks _ _ _ _ _ _ (by simp [restingState])

theorem linearTail_flag (regs : Fin 8 → Bool) (bank : Fin 9 → Word (baseWidth p μ)) :
    (linearTailResult (restingState regs (scriptEval p μ M linearScript bank) M.bits)).regs 2 =
      linearWordPass p μ M (bank 5) ![bank 0, bank 1, bank 2, bank 3] (bank 4) := by
  have h := CounterForPrograms.testResult_flag linearPorts
    (restingState regs (scriptEval p μ M linearScript bank) M.bits)
  simpa [linearTailResult, linearPorts, firstPorts, firstRegisters, restingState,
    linearWordPass, linearScript_result] using h

theorem quadraticTail_flag (regs : Fin 8 → Bool) (bank : Fin 14 → Word (baseWidth p μ)) :
    (quadraticTailResult (restingState regs (scriptEval p μ M quadraticScript bank) M.bits)).regs 2 =
      quadraticWordPass p μ M (bank 6) ![bank 0, bank 1, bank 2, bank 3]
        ![bank 4, bank 5] := by
  unfold quadraticTailResult
  rw [pairTest_flag _ _ _ _ _ _ (by simp [restingState])]
  change (!(CounterPrograms.isZero (scriptEval p μ M quadraticScript bank 12).val) ||
    !(CounterPrograms.isZero (scriptEval p μ M quadraticScript bank 13).val)) = _
  rfl

theorem linearTail_search (regs : Fin 8 → Bool) (bank : Fin 9 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 5) = -1) :
    (linearTailResult (restingState regs (scriptEval p μ M linearScript bank) M.bits)).regs 2 =
      QuarticSearch.linearPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (wordValue p μ (bank 4)) := by
  rw [linearTail_flag, linearWordPass_eq p μ M _ _ _ hminus]

theorem quadraticTail_search (regs : Fin 8 → Bool) (bank : Fin 14 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 6) = -1) :
    (quadraticTailResult (restingState regs (scriptEval p μ M quadraticScript bank) M.bits)).regs 2 =
      QuarticSearch.quadraticPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (fun i => wordValue p μ (![bank 4, bank 5] i)) := by
  rw [quadraticTail_flag, quadraticWordPass_eq p μ M _ _ _ hminus]

end SubexponentialSAT.SubexpQuarticDivisorMachine

end OAI.Algorithms
