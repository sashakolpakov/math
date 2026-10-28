import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCandidateMaterializer

namespace OAI.Algorithms

/-!
# Finalize a materialized candidate assignment

The complete packed array is input on stack 8. A unary width word on stack 3
selects its first `n` bits, and stack 2 contains the accumulated label-validity
bit. The remaining padding is scanned by an actual finite zero-test program.
The output assignment is on stack 1 and the combined validity bit on stack 9.
-/

namespace SubexponentialSAT.SubexpCandidateFinalize

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram
open SubexponentialSAT.SubexpCandidateMaterializer
open SubexponentialSAT.SubexpFactorProgram

private def straight {r s : ℕ} : List (StructuredProgram.Atom r s) → StructuredProgram.Cmd r s
  | [] => .skip
  | a :: as => .seq (.atom a) (straight as)

private def straightResult {r s : ℕ} : List (StructuredProgram.Atom r s) →
    StructuredProgram.State r s → StructuredProgram.State r s
  | [], d => d
  | a :: as, d => straightResult as (a.eval d)

private theorem straight_eval {r s : ℕ} (as : List (StructuredProgram.Atom r s))
    (d : StructuredProgram.State r s) :
    StructuredProgram.Eval (straight as) as.length d (straightResult as d) := by
  induction as generalizing d with
  | nil => exact .skip d
  | cons a as ih =>
      simpa only [straight, straightResult, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom a d) (ih (a.eval d))

private def combineOps : List (StructuredProgram.Atom 3 10) :=
  [.pop 2 0 2, .pop 9 1 2, .band 0 0 1, .push 9 0,
    .set 0 false, .set 1 false, .set 2 false]

abbrev combineValidity : StructuredCalls.Cmd 3 10 := .base (straight combineOps)

theorem combineValidity_eval (assignment width : List Bool) (prior paddingValid : Bool) :
    StructuredCalls.Eval combineValidity 7
      (state [] assignment [prior] width [] [] [] [] [] [paddingValid])
      (outputState [] assignment width (prior && paddingValid)) := by
  have h := straight_eval combineOps
    (state [] assignment [prior] width [] [] [] [] [] [paddingValid])
  have heq : straightResult combineOps
      (state [] assignment [prior] width [] [] [] [] [] [paddingValid]) =
      outputState [] assignment width (prior && paddingValid) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;>
        simp [ state, store,
          Atom.eval, Atom.instr, State.ofCfg, execInstr, readRegs]
    · funext i
      fin_cases i <;>
        simp [ state, store,
          Atom.eval, Atom.instr, State.ofCfg, execInstr, readRegs]
  rw [heq] at h
  exact .base (by simpa only [combineOps, List.length_cons, List.length_nil] using h)

abbrev command : StructuredCalls.Cmd 3 10 :=
  .seq copyWidth (.seq takeLow (.seq restoreLow (.seq validateHigh combineValidity)))

def program := StructuredCalls.compiled command (8 : Fin 10) 1

theorem command_size : StructuredCalls.size command = 34 := rfl

def workCost (assignmentWidth paddingWidth : ℕ) : ℕ :=
  14 * assignmentWidth + 4 * paddingWidth + 26

theorem command_eval (assignment padding width : List Bool) (prior : Bool)
    (hw : width.length = assignment.length) :
    StructuredCalls.Eval command (workCost assignment.length padding.length)
      (inputState [] [prior] width (assignment ++ padding))
      (outputState [] assignment width (prior && allZero padding)) := by
  have h := (copyWidth_eval [] [prior] width (assignment ++ padding)).seq
    ((takeLow_eval [] [prior] width assignment padding hw).seq
      ((restoreLow_eval [] [prior] width assignment padding).seq
        ((validateHigh_eval [] assignment [prior] width padding).seq
          (combineValidity_eval assignment width prior (allZero padding)))))
  convert h using 1 ; simp only [workCost, hw] ; ring

theorem trace (assignment padding width : List Bool) (prior : Bool)
    (hw : width.length = assignment.length) :
    Trace program (workCost assignment.length padding.length + 1)
      ((inputState [] [prior] width (assignment ++ padding)).withPC (some program.entry))
      ((outputState [] assignment width (prior && allZero padding)).withPC none) :=
  StructuredCalls.compiled_halt_trace (command_eval assignment padding width prior hw) 8 1

theorem validity (assignment padding : List Bool) (prior : Bool) :
    (prior && allZero padding) =
      decide (prior = true ∧ BinaryArithmetic.toNat (assignment ++ padding) <
        2 ^ assignment.length) := by
  rw [UnaryValidity.result_correct assignment padding]
  cases prior <;> simp

/-- The actual extraction works for any requested prefix with enough data. -/
theorem prefix_trace (array width : List Bool) (prior : Bool) (hlen : width.length ≤ array.length) :
    Trace program (workCost width.length (array.length - width.length) + 1)
      ((inputState [] [prior] width array).withPC (some program.entry))
      ((outputState [] (array.take width.length) width
        (prior && allZero (array.drop width.length))).withPC none) := by
  have h := trace (array.take width.length) (array.drop width.length) width prior
    (by simp [List.length_take, Nat.min_eq_left hlen])
  simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left hlen, List.length_drop] using h

theorem primitive_execution (assignment padding width : List Bool) (prior : Bool)
    (hw : width.length = assignment.length) :
    Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * (workCost assignment.length padding.length + 1))
      (BitProgram.primitiveCfg program
        ((inputState [] [prior] width (assignment ++ padding)).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((outputState [] assignment width (prior && allZero padding)).withPC none)) :=
  BitProgram.primitive_trace program (trace assignment padding width prior hw)

theorem lifted_eval {R S : ℕ} (register : Fin 3 → Fin R) (stack : Fin 10 → Fin S)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (frame : StructuredProgram.State R S) (assignment padding width : List Bool) (prior : Bool)
    (hw : width.length = assignment.length) :
    StructuredCalls.Eval (.call (ProgramLinking.liftProgram program register stack))
      (workCost assignment.length padding.length + 1)
      (StructuredCalls.embedState register stack frame
        (inputState [] [prior] width (assignment ++ padding)))
      (StructuredCalls.embedState register stack frame
        (outputState [] assignment width (prior && allZero padding))) :=
  StructuredCalls.eval_call_lifted program register stack frame hregister hstack
    (trace assignment padding width prior hw)

end SubexponentialSAT.SubexpCandidateFinalize

end OAI.Algorithms
