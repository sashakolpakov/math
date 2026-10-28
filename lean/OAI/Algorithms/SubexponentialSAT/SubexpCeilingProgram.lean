import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CeilingDivisionPrograms
import OAI.Algorithms.SubexponentialSAT.ModularQuotientPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpPackingParameters

namespace OAI.Algorithms

/-!
# The actual binary program for the packed dimension

Binary long division yields quotient and remainder. A finite zero test and
conditional increment then produce the ceiling. The input-dependent values are
stack words throughout; the control table is fixed.
-/

namespace SubexponentialSAT.SubexpCeilingProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.ModularQuotientArithmetic

abbrev Data := StructuredProgram.State 8 8
abbrev Regs := Fin 8 → Bool

def state (regs : Regs) (remainder modulus input quotient : List Bool) : Data :=
  ⟨regs, ModularQuotientPrograms.quotientStacks remainder modulus input quotient⟩

def inputState (regs : Regs) (modulus input : List Bool) : Data :=
  state regs [] modulus input []

abbrev command : StructuredCalls.Cmd 8 8 :=
  .seq (.call ModularQuotientPrograms.quotientProgram) CeilingDivisionPrograms.roundCmd

def program := StructuredCalls.compiled command (6 : Fin 8) 7

theorem command_size : StructuredCalls.size command = 114 := rfl

def runtimeBound (modulus input : List Bool) : ℕ :=
  100 * (modulus.length + input.length + 1) ^ 2 +
    8 * (modulus.length + 2 * input.length) + 16

theorem runtimeBound_le (modulus input : List Bool) {L : ℕ}
    (hm : modulus.length ≤ L) (hx : input.length ≤ L) :
    runtimeBound modulus input ≤ 500 * (L + 1) ^ 2 := by
  have hs : modulus.length + input.length + 1 ≤ 2 * L + 1 := by omega
  have hp := Nat.pow_le_pow_left hs 2
  dsimp [runtimeBound]
  nlinarith

def Output (modulus input : List Bool) (d : Data) : Prop :=
  BinaryArithmetic.toNat (d.stacks 7) = ChunkPartition.count (BinaryArithmetic.toNat input) (BinaryArithmetic.toNat modulus) ∧
  (d.stacks 7).length ≤ input.length + 1 ∧
  ∀ j : Fin 8, j ≠ 7 → d.stacks j =
    ModularQuotientPrograms.quotientStacks (divide modulus input).2 modulus []
      (divide modulus input).1 j

theorem command_eval (regs : Regs) (modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ n d, StructuredCalls.Eval command n (inputState regs modulus input) d ∧
      Output modulus input d ∧ n + 1 ≤ runtimeBound modulus input := by
  obtain ⟨rf, n₁, hn₁, ht⟩ := ModularQuotientPrograms.quotient_correct regs modulus input
  let mid := state rf (divide modulus input).2 modulus [] (divide modulus input).1
  have hfirst : StructuredCalls.Eval (.call ModularQuotientPrograms.quotientProgram) n₁
      (inputState regs modulus input) mid := .call _ ht
  obtain ⟨n₂, d, hround, hout, hn₂⟩ := CeilingDivisionPrograms.round_eval mid rfl
  have hl₀ : (mid.stacks 0).length = modulus.length + input.length :=
    divide_remainder_length modulus input
  have hl₇ : (mid.stacks 7).length = input.length :=
    divide_quotient_length modulus input
  refine ⟨n₁ + n₂, d, .seq hfirst hround, ?_, ?_⟩
  · refine ⟨?_, ?_, hout.2⟩
    · have hv : BinaryArithmetic.toNat (d.stacks 7) = BinaryArithmetic.toNat (divide modulus input).1 +
          if BinaryArithmetic.toNat (divide modulus input).2 = 0 then 0 else 1 := by
        simpa [mid, state, CounterPrograms.value_eq_toNat] using
          CeilingDivisionPrograms.round_value mid d hout
      rw [divide_quotient_correct modulus input hm,
        divide_remainder_correct modulus input hm] at hv
      rw [ChunkPartition.count_eq_div_add_ite hm]
      exact hv
    · simpa only [hl₇] using CeilingDivisionPrograms.round_length mid d hout
  · have hb : n₂ ≤ 8 * ((modulus.length + input.length) + input.length) + 15 := by
      simpa only [CeilingDivisionPrograms.roundBound, hl₀, hl₇] using hn₂
    dsimp [runtimeBound]
    omega

theorem run_output (regs : Regs) (modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ d, Output modulus input d ∧
      BitProgram.RunsIn program (runtimeBound modulus input)
        ((inputState regs modulus input).withPC (some program.entry)) (d.withPC none) := by
  obtain ⟨n, d, he, hout, hn⟩ := command_eval regs modulus input hm
  exact ⟨d, hout, n + 1, hn, StructuredCalls.compiled_halt_trace he 6 7⟩

theorem output_remainder (modulus input : List Bool) (d : Data)
    (hm : 0 < BinaryArithmetic.toNat modulus) (h : Output modulus input d) :
    BinaryArithmetic.toNat (d.stacks 0) = BinaryArithmetic.toNat input % BinaryArithmetic.toNat modulus := by
  rw [h.2.2 0 (by decide)]
  exact divide_remainder_correct modulus input hm

theorem output_modulus (modulus input : List Bool) (d : Data) (h : Output modulus input d) :
    d.stacks 5 = modulus := h.2.2 5 (by decide)

theorem output_work (modulus input : List Bool) (d : Data) (h : Output modulus input d)
    (j : Fin 8) (hj : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 6) :
    d.stacks j = [] := by
  rcases hj with rfl | rfl | rfl | rfl | rfl <;> exact h.2.2 _ (by decide)

/-- With the actual schedule words, the same finite program computes `D(n)`.
The positive-divisor premise is discharged by the previously checked guard. -/
theorem packed_dimension (regs : Regs) (n : ℕ) (hn : SubexpPackingParameters.GoodInput n)
    (exponent input : List Bool) (hu : BinaryArithmetic.toNat exponent = SubexpPackingParameters.u n)
    (hx : BinaryArithmetic.toNat input = n) :
    ∃ d : Data, BinaryArithmetic.toNat (d.stacks 7) = SubexpPackingParameters.D n ∧
      (d.stacks 7).length ≤ input.length + 1 ∧
      BitProgram.RunsIn program (runtimeBound exponent input)
        ((inputState regs exponent input).withPC (some program.entry)) (d.withPC none) := by
  have hm : 0 < BinaryArithmetic.toNat exponent := by
    rw [hu]
    exact SubexpPackingParameters.ell_pos hn
  obtain ⟨d, hout, hr⟩ := run_output regs exponent input hm
  refine ⟨d, ?_, hout.2.1, hr⟩
  simpa only [hu, hx, SubexpPackingParameters.D, SubexpPackingParameters.ell] using hout.1

theorem primitive_output (regs : Regs) (modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ d, Output modulus input d ∧
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * runtimeBound modulus input)
        (BitProgram.primitiveCfg program
          ((inputState regs modulus input).withPC (some program.entry)))
        (BitProgram.primitiveCfg program (d.withPC none)) := by
  obtain ⟨d, hout, hr⟩ := run_output regs modulus input hm
  exact ⟨d, hout, BitProgram.primitive_execution program hr⟩

/-- Fixed port maps preserve unrelated caller data. -/
theorem lifted_output {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 8 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : StructuredProgram.State R S) (regs : Regs) (modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ n d, n ≤ runtimeBound modulus input ∧ Output modulus input d ∧
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram program register stack)) n
        (StructuredCalls.embedState register stack frame (inputState regs modulus input))
        (StructuredCalls.embedState register stack frame d) := by
  obtain ⟨n, d, he, hout, hn⟩ := command_eval regs modulus input hm
  exact ⟨n + 1, d, hn, hout,
    StructuredCalls.eval_call_lifted program register stack frame hregister hstack
      (StructuredCalls.compiled_halt_trace he 6 7)⟩

end SubexponentialSAT.SubexpCeilingProgram

end OAI.Algorithms
