import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScanPrimitives
import OAI.Algorithms.SubexponentialSAT.TruncatedConvolution

namespace OAI.Algorithms

/-!
# Fixed finite control for triangular, truncated convolution

Polynomial coefficients occupy equal-width flat cells. Both input arrays have
D cells. The left array is consumed; the right array is retained. The output
array is preallocated with D zero cells. Unary loop counters and indices are
runtime stacks, so changing D does not change this control program.

The scalar product-and-accumulate command is inserted as a fixed command. Its
concrete implementation uses the quartic multiplier and the persistent cell
updater; it is never a semantic-function instruction.
-/

namespace SubexponentialSAT.SubexpConvolutionControl

open BitProgram StructuredCalls SubexpScanPrimitives

abbrev Data := State 16 256
abbrev Code := Cmd 16 256

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

/-- Order-preserving copy; stack 120 is reserved scratch. -/
def copy (src dst : Fin 256) : Code := .call (StackRoutines.copyProgram src dst 120 0 1)

def clear (src : Fin 256) : Code := .call (StackRoutines.clearProgram src 0 1)

def appendIndex (index : Fin 256) : Code :=
  (.base (.atom (.set 0 false))) ;; (.base (.atom (.push index 0)))

def popToken (counter : Fin 256) : Code := .base (.atom (.pop counter 0 1))

def test (counter : Fin 256) (flag : Fin 16) : Code := .base (.atom (.peek counter 0 flag))

/-- Stack 104 holds the unary coefficient width, and 121--122 are scratch. -/
def takeCell (src dst : Fin 256) : Code := takeWord 104 121 122 src dst 0 1

/-- One actual (i,j) iteration. The inserted fixed command consumes operands
198/199 and accumulates into output cell indexed by unary stack 103. -/
def innerStep (pair : Code) : Code :=
  popToken 109 ;; takeCell 108 199 ;; copy 110 198 ;; pair ;; appendIndex 103

def innerLoop (pair : Code) : Code :=
  test 109 15 ;; .while 15 (innerStep pair ;; test 109 15)

/-- At row i, stack 106 has D-i tokens. Its full copy limits the inner loop
to D-i products; the outer copy loses one token for the next row. -/
def outerStep (pair : Code) : Code :=
  copy 106 109 ;; popToken 106 ;; takeCell 100 110 ;; copy 101 108 ;; copy 105 103 ;;
    innerLoop pair ;; clear 108 ;; clear 109 ;; clear 103 ;; clear 110 ;; appendIndex 105

def outerLoop (pair : Code) : Code :=
  test 106 14 ;; .while 14 (outerStep pair ;; test 106 14)

def command (pair : Code) : Code := outerLoop pair ;; clear 105

def program (pair : Code) := compiled (command pair) 100 102

/-- Finite control size is independent of every array dimension and value. -/
theorem command_size (pair : Code) : size (command pair) = size pair + 93 := by
  norm_num [command, outerLoop, outerStep, innerLoop, innerStep, seq, test,
    popToken, takeCell, takeWord, copy, clear, appendIndex, size, StructuredProgram.size,
    StackRoutines.copyProgram, StackRoutines.clearProgram,
    ArrayPrograms.countedTransferProgram, StackRoutines.transferProgram]
  omega

def afterClear (d : Data) (src : Fin 256) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks src []⟩

theorem clear_eval (d : Data) (src : Fin 256) :
    Eval (clear src) (2 * (d.stacks src).length + 3) d (afterClear d src) := by
  apply Eval.call
  have h := StackRoutines.halt_after_trace _
    (StackRoutines.clearProgram_trace src (0 : Fin 16) 1 d.regs d.stacks) 2 rfl rfl
  simpa [afterClear, clear, StackRoutines.clearResult, StackRoutines.clearProgram,
    StackRoutines.clearStacks, StructuredProgram.State.withPC, Nat.add_assoc] using h

def afterAppendIndex (d : Data) (index : Fin 256) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks index (false :: d.stacks index)⟩

theorem appendIndex_eval (d : Data) (index : Fin 256) :
    Eval (appendIndex index) 2 d (afterAppendIndex d index) := by
  have h₁ := StructuredProgram.Eval.atom (StructuredProgram.Atom.set 0 false) d
  have h₂ := StructuredProgram.Eval.atom (StructuredProgram.Atom.push index 0)
    ((StructuredProgram.Atom.set 0 false).eval d)
  simpa [appendIndex, seq, afterAppendIndex, StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
    StructuredProgram.State.withPC, execInstr] using Eval.seq (.base h₁) (.base h₂)

end SubexponentialSAT.SubexpConvolutionControl

end OAI.Algorithms
