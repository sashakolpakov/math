import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpWordLiftMachine
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-!
# Reduce and normalize an arbitrary raw word using the existing fixed program

This module reuses `SubexpWordLiftMachine.program` without modifying its
instructions. Input6 is any bit list, modulus5 is preserved, shape7 supplies
the output width, and output0 receives the normalized remainder. All other
stacks are empty on return. In particular the input need not have source-field
width, as required when reducing a target-ring coordinate to the source field.
-/

namespace SubexponentialSAT.SubexpRawWordReduction

open BitProgram ProgramLinking BinaryArithmetic StructuredCalls
open ModularDivisionPrograms ModularRingPrograms

abbrev program : Program 8 8 101 := SubexpWordLiftMachine.program
abbrev runtimeBound := SubexpWordLiftMachine.runtimeBound

def outputBits (shape modulus input : List Bool) : List Bool :=
  ModularArithmetic.padTo shape (ModularArithmetic.reduce modulus input)

@[simp] theorem output_length (shape modulus input : List Bool) :
    (outputBits shape modulus input).length = shape.length :=
  ModularArithmetic.padTo_length _ _

theorem output_value (shape modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hwidth : BinaryArithmetic.toNat modulus ≤ 2 ^ shape.length) :
    BinaryArithmetic.toNat (outputBits shape modulus input) = BinaryArithmetic.toNat input % BinaryArithmetic.toNat modulus := by
  unfold outputBits
  rw [padTo_value_of_lt]
  · exact ModularArithmetic.reduce_correct modulus input hm
  · rw [ModularArithmetic.reduce_correct modulus input hm]
    exact (Nat.mod_lt _ hm).trans_le hwidth

theorem output_eq_fixedBits (shape modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hwidth : BinaryArithmetic.toNat modulus ≤ 2 ^ shape.length) :
    outputBits shape modulus input =
      SubexpLiftRing.fixedBits shape.length (BinaryArithmetic.toNat input % BinaryArithmetic.toNat modulus) := by
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · simp only [output_length, SubexpLiftRing.fixedBits_length]
  · rw [output_value shape modulus input hm hwidth,
      SubexpLiftRing.toNat_fixedBits_of_lt _ _ ((Nat.mod_lt _ hm).trans_le hwidth)]

def inputState (regs : Fin 8 → Bool) (modulus input shape : List Bool) : State 8 8 :=
  ⟨regs, extendSeven (resting [] modulus input) shape⟩

def outputState (regs : Fin 8 → Bool) (modulus output : List Bool) : State 8 8 :=
  ⟨regs, extendSeven (resting output modulus []) []⟩

@[simp] theorem outputState_output (regs : Fin 8 → Bool) (modulus output : List Bool) :
    (outputState regs modulus output).stacks 0 = output := rfl

@[simp] theorem outputState_modulus (regs : Fin 8 → Bool) (modulus output : List Bool) :
    (outputState regs modulus output).stacks 5 = modulus := rfl

theorem outputState_work (regs : Fin 8 → Bool) (modulus output : List Bool)
    (i : Fin 8) (h0 : i ≠ 0) (h5 : i ≠ 5) :
    (outputState regs modulus output).stacks i = [] := by
  fin_cases i <;> simp_all [outputState, extendSeven, resting, seven]

private theorem embedded_seven {l : ℕ} (pc : Option (Fin l))
    (regs frameRegs : Fin 8 → Bool) (base frameBase : Fin 7 → List Bool)
    (shape : List Bool) :
    embedCfg id sevenPorts id none
      (⟨none, frameRegs, extendSeven frameBase shape⟩ : Cfg 8 8 l)
      ⟨pc, regs, base⟩ = ⟨pc, regs, extendSeven base shape⟩ := by
  apply ModularRingPrograms.embed_ports sevenPorts sevenPorts_injective
  · intro i
    fin_cases i <;> rfl
  · intro i hi
    fin_cases i
    · exact False.elim (hi ⟨0, rfl⟩)
    · exact False.elim (hi ⟨1, rfl⟩)
    · exact False.elim (hi ⟨2, rfl⟩)
    · exact False.elim (hi ⟨3, rfl⟩)
    · exact False.elim (hi ⟨4, rfl⟩)
    · exact False.elim (hi ⟨5, rfl⟩)
    · exact False.elim (hi ⟨6, rfl⟩)
    · rfl

/-- Actual execution for unrestricted input words and runtime output width.
The program is total even for zero modulus; positivity is needed only for
the modular-value interpretation given by `output_value`. -/
theorem run (regs : Fin 8 → Bool) (modulus input shape : List Bool) :
    ∃ finalRegs, RunsIn program
      (runtimeBound input.length shape.length modulus.length)
      ((inputState regs modulus input shape).withPC (some program.entry))
      ((outputState finalRegs modulus (outputBits shape modulus input)).withPC none) := by
  obtain ⟨r₁, hr⟩ := remainder_correct regs modulus input
  have lifted := liftProgram_runsIn remainderProgram id sevenPorts
    (⟨none, regs, extendSeven (resting [] modulus []) shape⟩ : Cfg 8 8 89)
    Function.injective_id sevenPorts_injective hr
  rw [embedded_seven, embedded_seven] at lifted
  obtain ⟨r₂, hn⟩ := normalize_correct r₁ (ModularArithmetic.reduce modulus input) shape modulus
  have total := link_runsIn (liftProgram remainderProgram id sevenPorts) normalizeProgram
    lifted rfl hn
  refine ⟨r₂, ?_⟩
  simpa [program, SubexpWordLiftMachine.program, runtimeBound,
    SubexpWordLiftMachine.runtimeBound, inputState, outputState, outputBits,
    ModularArithmetic.reduce_length, normalizationState, extendSeven, resting, seven,
    relabelCfg, relocatePc, Nat.add_assoc] using total

abbrev command : Cmd 8 8 := .call program

theorem command_eval (regs : Fin 8 → Bool) (modulus input shape : List Bool) :
    ∃ n ≤ runtimeBound input.length shape.length modulus.length, ∃ finalRegs,
      Eval command n (inputState regs modulus input shape)
        (outputState finalRegs modulus (outputBits shape modulus input)) := by
  obtain ⟨finalRegs, n, hn, ht⟩ := run regs modulus input shape
  exact ⟨n, hn, finalRegs, Eval.call program ht⟩

theorem runtimeBound_le (inputWidth targetWidth modulusWidth : ℕ) :
    runtimeBound inputWidth targetWidth modulusWidth ≤
      110 * (inputWidth + targetWidth + modulusWidth + 1) ^ 2 := by
  have hbase : modulusWidth + inputWidth + 1 ≤ inputWidth + targetWidth + modulusWidth + 1 := by omega
  have hquad := Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hbase 2)
  have hsq : inputWidth + targetWidth + modulusWidth + 1 ≤
      (inputWidth + targetWidth + modulusWidth + 1) ^ 2 := by
    nlinarith
  unfold runtimeBound SubexpWordLiftMachine.runtimeBound
  nlinarith

theorem primitive_run (regs : Fin 8 → Bool) (modulus input shape : List Bool) :
    ∃ finalRegs, Computation.RunsIn (primitive program).step
      (primitiveOverhead program * runtimeBound input.length shape.length modulus.length)
      (primitiveCfg program ((inputState regs modulus input shape).withPC (some program.entry)))
      (primitiveCfg program
        ((outputState finalRegs modulus (outputBits shape modulus input)).withPC none)) := by
  obtain ⟨finalRegs, ht⟩ := run regs modulus input shape
  exact ⟨finalRegs, BitProgram.primitive_execution _ ht⟩

end SubexponentialSAT.SubexpRawWordReduction

end OAI.Algorithms
