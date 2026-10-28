import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticTestMachine
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-!
# A shared word bank for both quartic divisor tests

Using the same fourteen-word bank lets repeated linear and quadratic tests
retain all coefficient inputs and the prepared minus-one word. Only the
divisor words need replacing between calls.
-/

namespace SubexponentialSAT.SubexpQuarticSharedTest

open BitProgram StructuredCalls
open SubexpLiftRing SubexpQuarticRing SubexpQuarticMachine SubexpQuarticTestProgram

/-- Coefficients occupy 0--3, the linear divisor is 4, and minus one is 6.
The output is 12, matching the first quadratic-remainder output. -/
def linearScript : List (Instr 14) :=
  [⟨.mul, 7, 4, 6⟩,
   ⟨.add, 10, 3, 7⟩,
   ⟨.mul, 10, 7, 10⟩,
   ⟨.add, 10, 2, 10⟩,
   ⟨.mul, 10, 7, 10⟩,
   ⟨.add, 10, 1, 10⟩,
   ⟨.mul, 10, 7, 10⟩,
   ⟨.add, 12, 0, 10⟩]

def linearPorts : CounterForPrograms.Ports 8 23 :=
  firstPorts (bankPort (12 : Fin 14)) (tempPort 14) (by simp)

abbrev linearTail : Cmd 8 23 := CounterForPrograms.testCmd linearPorts
abbrev linearCmd : Cmd 8 23 := .seq (scriptCmd linearScript) linearTail
def linearProgram := compiled linearCmd (bankPort (4 : Fin 14)) (bankPort (12 : Fin 14))

@[simp] theorem linearScript_length : linearScript.length = 8 := rfl

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

theorem linearScript_result (bank : Fin 14 → Word (baseWidth p μ)) :
    scriptEval p μ M linearScript bank 12 =
      linearWord p μ M (bank 6) ![bank 0, bank 1, bank 2, bank 3] (bank 4) := rfl

theorem linearScript_preserves (bank : Fin 14 → Word (baseWidth p μ)) (i : Fin 7) :
    scriptEval p μ M linearScript bank (Fin.castAdd 7 i) = bank (Fin.castAdd 7 i) := by
  fin_cases i <;> rfl

theorem linear_eval (regs : Fin 8 → Bool) (bank : Fin 14 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 6) = -1) :
    ∃ n finalRegs,
      n ≤ 50000 * (baseWidth p μ + 1)^2 ∧
      Eval linearCmd n (restingState regs bank M.bits)
        (restingState finalRegs (scriptEval p μ M linearScript bank) M.bits) ∧
      finalRegs 2 = QuarticSearch.linearPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (wordValue p μ (bank 4)) := by
  obtain ⟨n, finalRegs, hn, he⟩ := script_run p μ M linearScript regs bank
  simp only [linearScript_length] at hn
  let d := restingState finalRegs (scriptEval p μ M linearScript bank) M.bits
  let e := CounterForPrograms.testResult linearPorts d
  have hempty : d.stacks linearPorts.scratch = [] := by
    simp [d, linearPorts, firstPorts, restingState]
  have htail := CounterForPrograms.test_eval linearPorts d hempty
  have hlen : (d.stacks linearPorts.counter).length = baseWidth p μ := by
    change (scriptEval p μ M linearScript bank 12).val.length = baseWidth p μ
    exact (scriptEval p μ M linearScript bank 12).property
  rw [hlen] at htail
  have hs : e.stacks = d.stacks :=
    CounterForPrograms.testResult_stacks linearPorts d hempty
  have heq : e = restingState e.regs (scriptEval p μ M linearScript bank) M.bits := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hs
  have hf : e.regs 2 = QuarticSearch.linearPass (p^μ)
      (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
      (wordValue p μ (bank 4)) := by
    have hflag := CounterForPrograms.testResult_flag linearPorts d
    change e.regs 2 = _
    change e.regs 2 = _ at hflag
    rw [hflag]
    have hcounter : d.stacks linearPorts.counter =
        (scriptEval p μ M linearScript bank 12).val := rfl
    rw [hcounter, linearScript_result]
    exact linearWordPass_eq p μ M (bank 6) ![bank 0, bank 1, bank 2, bank 3]
      (bank 4) hminus
  refine ⟨n + (8 * baseWidth p μ + 7), e.regs, ?_, ?_, hf⟩
  · exact SubexpQuarticTestMachine.linear_cost (baseWidth p μ) n hn
  · rw [← heq]
    exact he.seq htail

theorem linear_run (regs : Fin 8 → Bool) (bank : Fin 14 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 6) = -1) :
    ∃ finalRegs,
      RunsIn linearProgram (50000 * (baseWidth p μ + 1)^2 + 1)
        ((restingState regs bank M.bits).withPC (some linearProgram.entry))
        ((restingState finalRegs (scriptEval p μ M linearScript bank) M.bits).withPC none) ∧
      finalRegs 2 = QuarticSearch.linearPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (wordValue p μ (bank 4)) := by
  obtain ⟨n, finalRegs, hn, he, hf⟩ := linear_eval p μ M regs bank hminus
  exact ⟨finalRegs, ⟨n + 1, Nat.add_le_add_right hn 1,
    compiled_halt_trace he (bankPort (4 : Fin 14)) (bankPort (12 : Fin 14))⟩, hf⟩

theorem quadratic_run (regs : Fin 8 → Bool) (bank : Fin 14 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 6) = -1) :
    ∃ finalRegs,
      RunsIn SubexpQuarticTestMachine.quadraticProgram (75000 * (baseWidth p μ + 1)^2 + 1)
        ((restingState regs bank M.bits).withPC
          (some SubexpQuarticTestMachine.quadraticProgram.entry))
        ((restingState finalRegs
          (scriptEval p μ M SubexpQuarticDivisorMachine.quadraticScript bank) M.bits).withPC none) ∧
      finalRegs 2 = QuarticSearch.quadraticPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (fun i => wordValue p μ (![bank 4, bank 5] i)) := by
  obtain ⟨out, hr, hs, hf⟩ := SubexpQuarticTestMachine.quadratic_run p μ M regs bank hminus
  have heq : out = restingState out.regs
      (scriptEval p μ M SubexpQuarticDivisorMachine.quadraticScript bank) M.bits := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hs
  refine ⟨out.regs, ?_, hf⟩
  rw [← heq]
  exact hr

end SubexponentialSAT.SubexpQuarticSharedTest

end OAI.Algorithms
