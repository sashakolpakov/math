import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.SubexpAlphabetProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockSearchPreparation
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives

namespace OAI.Algorithms

/-! # Physical prime normalization and scalar-alphabet production for quartic search -/

namespace SubexponentialSAT.SubexpQuarticInitialCalls

open BitProgram StructuredCalls SubexpEnumerationPayload SubexpAlphabetProgram
open Subexp.BlockSearchPreparation (restrictState lifted_call)

abbrev Data := State 14 35

def normalizerRegisters (i : Fin 3) : Fin 14 := Fin.castAdd 11 i
def normalizerStacks : Fin 3 → Fin 35 := ![34, 0, 1]
abbrev normalize : Cmd 14 35 := .call (ProgramLinking.liftProgram
  CounterNormalizeProgram.program normalizerRegisters normalizerStacks)

theorem normalizerRegisters_injective : Function.Injective normalizerRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 14 => k.val) h)

theorem normalizerStacks_injective : Function.Injective normalizerStacks := by decide

theorem normalize_call (p : ℕ) [Fact p.Prime] (d : Data) (bits : List Bool)
    (hbits : d.stacks 34 = bits) (hvalue : CounterPrograms.value bits = p)
    (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = []) :
    ∃ n next,
      n ≤ 9 * bits.length + 21 ∧ Eval normalize n d next ∧
      next.stacks 34 = primeWord p ∧ next.stacks 0 = [] ∧ next.stacks 1 = [] ∧
      (∀ j : Fin 35, j ≠ 34 → j ≠ 0 → j ≠ 1 → next.stacks j = d.stacks j) := by
  have hp : 0 < CounterPrograms.value bits := hvalue.symm ▸ (Fact.out : p.Prime).pos
  have hrestrict : restrictState normalizerRegisters normalizerStacks d =
      CounterNormalizeProgram.state (d.regs ∘ normalizerRegisters) bits [] := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [restrictState, normalizerStacks, CounterNormalizeProgram.state, hbits, h0, h1]
  have hr := CounterNormalizeProgram.normalize_runs (d.regs ∘ normalizerRegisters) bits hp
  rw [← hrestrict] at hr
  have hcanonical : SubexpLiftRing.fixedBits (Nat.log2 (CounterPrograms.value bits) + 1)
      (CounterPrograms.value bits) = primeWord p := by
    simp only [hvalue, Nat.log2_eq_log_two, primeWord, scalarWidth]
  rw [hcanonical] at hr
  let out := CounterNormalizeProgram.state CounterNormalizeProgram.zeroRegs (primeWord p) []
  let next := embedState normalizerRegisters normalizerStacks d out
  obtain ⟨n, hn, he⟩ := lifted_call CounterNormalizeProgram.program
    normalizerRegisters normalizerStacks normalizerRegisters_injective normalizerStacks_injective
    d out _ hr
  refine ⟨n, next, hn, he, ?_, ?_, ?_, ?_⟩
  · exact embedState_stack normalizerRegisters normalizerStacks d out normalizerStacks_injective 0
  · exact embedState_stack normalizerRegisters normalizerStacks d out normalizerStacks_injective 1
  · exact embedState_stack normalizerRegisters normalizerStacks d out normalizerStacks_injective 2
  · intro j hj34 hj0 hj1
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [normalizerStacks]

def alphabetRegisters (i : Fin 6) : Fin 14 := Fin.castAdd 8 i
def alphabetStacks : Fin 6 → Fin 35 := ![34, 22, 0, 1, 2, 25]
abbrev alphabet : Cmd 14 35 := .call (ProgramLinking.liftProgram
  SubexpAlphabetProgram.program alphabetRegisters alphabetStacks)

theorem alphabetRegisters_injective : Function.Injective alphabetRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 14 => k.val) h)

theorem alphabetStacks_injective : Function.Injective alphabetStacks := by decide

/-- Generation consumes the normalized counter on 34, retaining a zero word
of its original width, and emits the exact ascending field alphabet on 25. -/
theorem alphabet_call (p : ℕ) [Fact p.Prime] (d : Data)
    (h34 : d.stacks 34 = primeWord p)
    (h22 : d.stacks 22 = []) (h0 : d.stacks 0 = []) (h1 : d.stacks 1 = [])
    (h2 : d.stacks 2 = []) (h25 : d.stacks 25 = []) :
    ∃ n next,
      n ≤ (p + 1) * (60 * scalarWidth p + 60) ∧ Eval alphabet n d next ∧
      next.stacks 25 = ProgramEncoding.encodeRecords
        ((QuarticSearch.elements p).map (scalarCode p).block) ∧
      next.stacks 22 = [] ∧ next.stacks 0 = [] ∧ next.stacks 1 = [] ∧ next.stacks 2 = [] ∧
      CounterPrograms.value (next.stacks 34) = 0 ∧ (next.stacks 34).length = scalarWidth p ∧
      (∀ j : Fin 35, j ≠ 34 → j ≠ 22 → j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 25 →
        next.stacks j = d.stacks j) := by
  have hrestrict : restrictState alphabetRegisters alphabetStacks d =
      inputState (primeWord p) (d.regs ∘ alphabetRegisters) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · funext i
      fin_cases i <;>
        simp [restrictState, alphabetStacks, inputState, h34, h22, h0, h1, h2, h25]
  obtain ⟨out, hout, hclean, hout1, hvalue, hlength, hr⟩ :=
    SubexpAlphabetProgram.program_runsIn_clean (primeWord p) (d.regs ∘ alphabetRegisters)
  rw [← hrestrict] at hr
  rw [primeWord_value, primeWord_length] at hr
  let next := embedState alphabetRegisters alphabetStacks d out
  obtain ⟨n, hn, he⟩ := lifted_call SubexpAlphabetProgram.program
    alphabetRegisters alphabetStacks alphabetRegisters_injective alphabetStacks_injective
    d out _ hr
  have hstack (i : Fin 6) : next.stacks (alphabetStacks i) = out.stacks i :=
    embedState_stack alphabetRegisters alphabetStacks d out alphabetStacks_injective i
  refine ⟨n, next, hn, he, ?_, (hstack 1).trans hout1,
    (hstack 2).trans hclean.1, (hstack 3).trans hclean.2.1, (hstack 4).trans hclean.2.2,
    ?_, ?_, ?_⟩
  · rw [show next.stacks 25 = out.stacks 5 from hstack 5, hout, alphabetWords_primeWord]
  · rw [show next.stacks 34 = out.stacks 0 from hstack 0]
    exact hvalue
  · rw [show next.stacks 34 = out.stacks 0 from hstack 0, hlength, primeWord_length]
  · intro j hj34 hj22 hj0 hj1 hj2 hj25
    apply embedState_stack_frame
    rintro ⟨i, hi⟩
    fin_cases i <;> simp_all [alphabetStacks]

end SubexponentialSAT.SubexpQuarticInitialCalls

end OAI.Algorithms
