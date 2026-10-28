import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularPrograms
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.SubexpModulusConstruction

namespace OAI.Algorithms

/-!
# Fixed programs for zero and one words

The width is supplied as a shape stack and is read cell by cell. The literal
seed is written by ordinary Boolean instructions. These routines do not
convert an unbounded natural value to bits during execution.
-/

namespace SubexponentialSAT.SubexpConstantPrograms

open BitProgram StructuredProgram StructuredCalls BinaryArithmetic

abbrev Regs := Fin 8 → Bool
abbrev Data := StructuredProgram.State 8 3

def state (r : Regs) (shape input : List Bool) : Data :=
  ⟨r, ModularPrograms.operandStacks shape input []⟩

def literal (one : Bool) : List Bool := if one then [true] else []

def seedRegs (one : Bool) (r : Regs) : Regs :=
  if one then Function.update r 0 true else r

abbrev seed (one : Bool) : StructuredCalls.Cmd 8 3 :=
  .base (if one then .seq (.atom (.set 0 true)) (.atom (.push 1 0)) else .skip)

private theorem update_input (shape input next : List Bool) :
    Function.update (ModularPrograms.operandStacks shape input []) 1 next =
      ModularPrograms.operandStacks shape next [] := by
  funext i
  fin_cases i <;> simp [ModularPrograms.operandStacks]

theorem seed_eval (one : Bool) (r : Regs) (shape : List Bool) :
    StructuredCalls.Eval (seed one) (if one then 2 else 0)
      (state r shape []) (state (seedRegs one r) shape (literal one)) := by
  cases one with
  | false => exact .base (.skip _)
  | true =>
      apply StructuredCalls.Eval.base
      have hs := StructuredProgram.Eval.atom (.set (0 : Fin 8) true) (state r shape [])
      have hp := StructuredProgram.Eval.atom (.push (1 : Fin 3) 0)
        (Atom.eval (.set (0 : Fin 8) true) (state r shape []))
      simpa [Atom.eval, Atom.instr, State.ofCfg, State.withPC, execInstr,
        seedRegs, literal, state, update_input] using StructuredProgram.Eval.seq hs hp

abbrev command (one : Bool) : StructuredCalls.Cmd 8 3 :=
  .seq (seed one) (.call ModularPrograms.paddingLEProgram)

/-- The two literal choices give fixed ten- and twelve-label programs. -/
def program (one : Bool) := StructuredCalls.compiled (command one) (0 : Fin 3) 0

theorem command_size (one : Bool) :
    StructuredCalls.size (command one) = if one then 11 else 9 := by
  cases one <;> rfl

theorem literal_length_le (one : Bool) (shape : List Bool)
    (hwidth : one = true → 0 < shape.length) : (literal one).length ≤ shape.length := by
  cases one <;> simp_all [literal]
  omega

theorem padded_eq_fixedBits (one : Bool) (shape : List Bool)
    (hwidth : one = true → 0 < shape.length) :
    ModularArithmetic.padTo shape (literal one) =
      SubexpLiftRing.fixedBits shape.length (bitVal one) := by
  have hl := literal_length_le one shape hwidth
  have hv : BinaryArithmetic.toNat (literal one) = bitVal one := by cases one <;> rfl
  have hfit : bitVal one < 2 ^ shape.length := by
    have h := ModularArithmetic.toNat_lt_pow_length
      (ModularArithmetic.padTo shape (literal one))
    rwa [ModularArithmetic.padTo_correct shape (literal one) hl,
      ModularArithmetic.padTo_length, hv] at h
  apply SubexpModulusConstruction.bits_eq_of_length_of_value
  · rw [ModularArithmetic.padTo_length, SubexpLiftRing.fixedBits_length]
  · rw [ModularArithmetic.padTo_correct shape (literal one) hl,
      SubexpLiftRing.toNat_fixedBits_of_lt _ _ hfit, hv]

/-- Exact finite-program execution, including the written seed and the final
halt. The input shape is consumed and both auxiliary stacks are emptied. -/
theorem run_literal (one : Bool) (r : Regs) (shape : List Bool)
    (hwidth : one = true → 0 < shape.length) :
    ∃ rf, BitProgram.Trace (program one)
      ((if one then 2 else 0) + (7 * shape.length + 6) + 1)
      ((state r shape []).withPC (some (program one).entry))
      ((state rf (SubexpLiftRing.fixedBits shape.length (bitVal one)) []).withPC none) := by
  obtain ⟨rf, ht, _⟩ := ModularPrograms.paddingLE_correct
    (seedRegs one r) shape (literal one) (literal_length_le one shape hwidth)
  have hc : StructuredCalls.Eval (.call ModularPrograms.paddingLEProgram)
      (7 * shape.length + 6) (state (seedRegs one r) shape (literal one))
      (state rf (ModularArithmetic.padTo shape (literal one)) []) := .call _ ht
  have he := StructuredCalls.Eval.seq (seed_eval one r shape) hc
  rw [padded_eq_fixedBits one shape hwidth] at he
  exact ⟨rf, StructuredCalls.compiled_halt_trace he 0 0⟩

theorem run_constant (one : Bool) (r : Regs) (shape : List Bool)
    (hwidth : one = true → 0 < shape.length) :
    ∃ rf, BitProgram.RunsIn (program one) (7 * shape.length + 9)
      ((state r shape []).withPC (some (program one).entry))
      ((state rf (SubexpLiftRing.fixedBits shape.length (bitVal one)) []).withPC none) := by
  obtain ⟨rf, ht⟩ := run_literal one r shape hwidth
  refine ⟨rf, _, ?_, ht⟩
  cases one <;> simp
  omega

theorem primitive_constant (one : Bool) (r : Regs) (shape : List Bool)
    (hwidth : one = true → 0 < shape.length) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive (program one)).step
      (BitProgram.primitiveOverhead (program one) * (7 * shape.length + 9))
      (BitProgram.primitiveCfg (program one)
        ((state r shape []).withPC (some (program one).entry)))
      (BitProgram.primitiveCfg (program one)
        ((state rf (SubexpLiftRing.fixedBits shape.length (bitVal one)) []).withPC none)) := by
  obtain ⟨rf, ht⟩ := run_constant one r shape hwidth
  exact ⟨rf, BitProgram.primitive_execution (program one) ht⟩

end SubexponentialSAT.SubexpConstantPrograms

end OAI.Algorithms
