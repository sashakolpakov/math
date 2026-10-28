import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticDivisorMachine

namespace OAI.Algorithms

/-!
# Primitive-machine quartic divisor tests

These are fixed finite programs. Coefficients, the prime-power modulus, and
the word denoting minus one are runtime data. The bounds include the scalar
operations, all operand copying, and the final nonzero tests.
-/

namespace SubexponentialSAT.SubexpQuarticTestMachine

open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing
open SubexponentialSAT.SubexpQuarticMachine SubexponentialSAT.SubexpQuarticDivisorMachine
open SubexponentialSAT.BitProgram

abbrev linearCmd : StructuredCalls.Cmd 8 18 := .seq (scriptCmd linearScript) linearTail
abbrev quadraticCmd : StructuredCalls.Cmd 8 23 := .seq (scriptCmd quadraticScript) quadraticTail

def linearProgram :=
  StructuredCalls.compiled linearCmd (bankPort (8 : Fin 9)) (bankPort (8 : Fin 9))

def quadraticProgram :=
  StructuredCalls.compiled quadraticCmd (bankPort (12 : Fin 14)) (bankPort (12 : Fin 14))

variable (p μ : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p μ)

/-- The runtime predecessor routine supplies this value equation for its
prepared constant. No conversion or search is performed by this lemma. -/
theorem preparedMinusOne_value (constant : Word (baseWidth p μ))
    (hconstant : BinaryArithmetic.toNat constant.val = BinaryArithmetic.toNat M.bits - 1) :
    wordValue p μ constant = -1 := by
  have hm : 1 ≤ p^μ := pow_pos (Fact.out : p.Prime).pos μ
  rw [wordValue, hconstant, M.value, Nat.cast_sub hm]
  simp

theorem linear_cost (B n : ℕ) (h : n ≤ 8 * 6100 * (B + 1)^2) :
    n + (8 * B + 7) ≤ 50000 * (B + 1)^2 := by
  nlinarith only [h, Nat.zero_le B]

theorem quadratic_cost (B n : ℕ) (h : n ≤ 12 * 6100 * (B + 1)^2) :
    n + (16 * B + 15) ≤ 75000 * (B + 1)^2 := by
  nlinarith only [h, Nat.zero_le B]

theorem linear_eval (regs : Fin 8 → Bool) (bank : Fin 9 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 5) = -1) :
    ∃ (n : ℕ) (out : StructuredCalls.State 8 18),
      n ≤ 50000 * (baseWidth p μ + 1)^2 ∧
      StructuredCalls.Eval linearCmd n (restingState regs bank M.bits) out ∧
      out.stacks = (restingState regs (scriptEval p μ M linearScript bank) M.bits).stacks ∧
      out.regs 2 = QuarticSearch.linearPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (wordValue p μ (bank 4)) := by
  obtain ⟨n, finalRegs, hn, he⟩ := script_run p μ M linearScript regs bank
  simp only [linearScript_length] at hn
  have htotal := linear_cost (baseWidth p μ) n hn
  refine ⟨n + (8 * baseWidth p μ + 7),
    linearTailResult (restingState finalRegs (scriptEval p μ M linearScript bank) M.bits),
    htotal, ?_, ?_, ?_⟩
  · exact he.seq (linearTail_eval p μ M finalRegs _)
  · exact linearTail_stacks p μ M finalRegs _
  · exact linearTail_search p μ M finalRegs bank hminus

theorem quadratic_eval (regs : Fin 8 → Bool) (bank : Fin 14 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 6) = -1) :
    ∃ (n : ℕ) (out : StructuredCalls.State 8 23),
      n ≤ 75000 * (baseWidth p μ + 1)^2 ∧
      StructuredCalls.Eval quadraticCmd n (restingState regs bank M.bits) out ∧
      out.stacks = (restingState regs (scriptEval p μ M quadraticScript bank) M.bits).stacks ∧
      out.regs 2 = QuarticSearch.quadraticPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (fun i => wordValue p μ (![bank 4, bank 5] i)) := by
  obtain ⟨n, finalRegs, hn, he⟩ := script_run p μ M quadraticScript regs bank
  simp only [quadraticScript_length] at hn
  have htotal := quadratic_cost (baseWidth p μ) n hn
  refine ⟨n + (16 * baseWidth p μ + 15),
    quadraticTailResult (restingState finalRegs (scriptEval p μ M quadraticScript bank) M.bits),
    htotal, ?_, ?_, ?_⟩
  · exact he.seq (quadraticTail_eval p μ M finalRegs _)
  · exact quadraticTail_stacks p μ M finalRegs _
  · exact quadraticTail_search p μ M finalRegs bank hminus

/-- The compiled finite program is directly usable by the program linker. -/
theorem linear_run (regs : Fin 8 → Bool) (bank : Fin 9 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 5) = -1) :
    ∃ out : StructuredCalls.State 8 18,
      RunsIn linearProgram (50000 * (baseWidth p μ + 1)^2 + 1)
        ((restingState regs bank M.bits).withPC (some linearProgram.entry))
        (out.withPC none) ∧
      out.stacks = (restingState regs (scriptEval p μ M linearScript bank) M.bits).stacks ∧
      out.regs 2 = QuarticSearch.linearPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (wordValue p μ (bank 4)) := by
  obtain ⟨n, out, hn, he, hs, hf⟩ := linear_eval p μ M regs bank hminus
  refine ⟨out, ⟨n + 1, Nat.add_le_add_right hn 1, ?_⟩, hs, hf⟩
  exact StructuredCalls.compiled_halt_trace he (bankPort (8 : Fin 9)) (bankPort (8 : Fin 9))

theorem quadratic_run (regs : Fin 8 → Bool) (bank : Fin 14 → Word (baseWidth p μ))
    (hminus : wordValue p μ (bank 6) = -1) :
    ∃ out : StructuredCalls.State 8 23,
      RunsIn quadraticProgram (75000 * (baseWidth p μ + 1)^2 + 1)
        ((restingState regs bank M.bits).withPC (some quadraticProgram.entry))
        (out.withPC none) ∧
      out.stacks = (restingState regs (scriptEval p μ M quadraticScript bank) M.bits).stacks ∧
      out.regs 2 = QuarticSearch.quadraticPass (p^μ)
        (fun i => wordValue p μ (![bank 0, bank 1, bank 2, bank 3] i))
        (fun i => wordValue p μ (![bank 4, bank 5] i)) := by
  obtain ⟨n, out, hn, he, hs, hf⟩ := quadratic_eval p μ M regs bank hminus
  refine ⟨out, ⟨n + 1, Nat.add_le_add_right hn 1, ?_⟩, hs, hf⟩
  exact StructuredCalls.compiled_halt_trace he (bankPort (12 : Fin 14)) (bankPort (12 : Fin 14))

end SubexponentialSAT.SubexpQuarticTestMachine

end OAI.Algorithms
