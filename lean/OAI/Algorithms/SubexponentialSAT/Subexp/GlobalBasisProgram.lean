import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRows
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisRowPrepare
import OAI.Algorithms.SubexponentialSAT.Subexp.GlobalBasisColumnBlocks
import OAI.Algorithms.SubexponentialSAT.SubexpComplementColumnBatch
import OAI.Algorithms.SubexponentialSAT.SubexpScopeCountSetup

namespace OAI.Algorithms

/-!
# Fixed global basis-bundle source program

All iteration counts, local matrices, and packing data are runtime words.
The program first selects the current type's local-search group.  It emits
inner matrices while counting colors downward, then emits the outer matrix;
prepending complete records gives the public outer-first, ascending-color
bundle order.  Every matrix row is generated in ascending ambient order.

Persistent inputs: scalar frame width/zero/one on 13/14/15, unary type index
32, packing table 33, universal type records 37, unary color count 38,
unary ambient dimension 46, grouped local
search records 47, unary block count 48, and unary leftover count 49.
The final encoded bundle is on 63.  Its records contain a framed unary
column count followed by a frame containing flat row-major scalar frames.
Port 39 is unused and preserved; no canonical-bit promise on a saved width
word is needed by the head-only Side filter.

This file defines the concrete finite source composition.  Its complete
execution/refinement proof is a separate remaining integration obligation.
-/

namespace SubexponentialSAT.Subexp.GlobalBasisProgram

open BitProgram StructuredCalls

abbrev Data := State 16 64
abbrev Code := Cmd 16 64

def regs8 : Fin 8 → Fin 16 := Fin.castAdd 8
def regs2 : Fin 2 → Fin 16 := Fin.castAdd 14
def low32 : Fin 32 → Fin 64 := Fin.castAdd 32
def low11 : Fin 11 → Fin 64 := Fin.castAdd 53

def copy (src dst : Fin 64) : Code := .call (StackRoutines.copyProgram src dst 31 0 1)
def transfer (src dst : Fin 64) : Code := .call (StackRoutines.transferProgram src dst 0 1)
def clear (src : Fin 64) : Code := .call (StackRoutines.clearProgram src 0 1)
def push (dst : Fin 64) (value : Bool) : Code := TupleProgram.pushConst dst 0 value
def move (src dst : Fin 64) : Code := .seq (transfer src 31) (transfer 31 dst)

def sequence (commands : List Code) : Code := commands.foldr Cmd.seq (.base .skip)
def clearList (ports : List (Fin 64)) : Code := sequence (ports.map clear)

def groupPorts : Fin 8 → Fin 64 := ![47, 32, 40, 16, 17, 18, 19, 20]
def getGroup : Code := .call
  (ProgramLinking.liftProgram GlobalBasisRecordLookup.program regs8 groupPorts)

/-- Temporary decoding for one inner matrix. Only the actual split word is
needed by the kernel-column generator; the other decoded fields are cleared. -/
def splitPorts : Fin 20 → Fin 64 :=
  ![40, 55, 16, 17, 18, 19, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 21, 22]
def getSplit : Code := .call
  (ProgramLinking.liftProgram GlobalBasisDataLookup.program regs8 splitPorts)
def kernelColumns : Code := .call
  (ProgramLinking.liftProgram GlobalBasisColumnBlocks.program regs8 low11)

def prepareInner : Code := sequence [
  getSplit, copy 48 0, copy 55 1, copy 17 10, push 3 false,
  kernelColumns, move 3 35, clearList [1, 10, 16, 17, 18, 19]]

def outerPorts : Fin 26 → Fin 64 :=
  ![0, 1, 2, 35, 3, 4, 5, 6, 7, 8, 9, 10, 11,
    16, 17, 18, 19, 20, 21, 22, 23, 24, 40, 38, 49, 25]
def outerColumns : Code := .call
  (ProgramLinking.liftProgram SubexpComplementColumnBatch.program regs8 outerPorts)
def prepareOuter : Code := sequence [copy 48 0, push 35 false, outerColumns]

def countPorts : Fin 2 → Fin 64 := ![16, 50]
def countColumns : Code := sequence [copy 35 16,
  .call (ProgramLinking.liftProgram SubexpScopeCountSetup.counterProgram regs2 countPorts)]

def row : Code := .call
  (ProgramLinking.liftProgram GlobalBasisRows.program id low32)

def rowStep : Code := sequence [
  .call GlobalBasisRowPrepare.program, copy 35 6, row,
  clearList [0, 1, 2, 3, 4, 5], push 34 true]

def rowPorts : UnaryForPrograms.Ports 16 64 := ⟨45, 0, 1⟩
def rows : Code := UnaryForPrograms.forCmd rowPorts rowStep

def matrix : Code := sequence [countColumns, copy 46 45, rows,
  clear 34, transfer 12 51]

def emitFrame (src dst tmp : Fin 64) (hne : tmp ≠ dst) : Code :=
  liftCommand (MatrixProgramSupport.emitFrame src dst tmp hne) src dst regs8 id

def emitMatrix : Code := sequence [
  emitFrame 51 56 57 (by decide), copy 50 58,
  emitFrame 58 56 57 (by decide), emitFrame 56 63 57 (by decide),
  push 63 true, clear 50, clear 35]

def innerStep : Code := sequence [prepareInner, matrix, emitMatrix]
def colorPorts : UnaryForPrograms.Ports 16 64 := ⟨55, 0, 1⟩
def innerMatrices : Code := UnaryForPrograms.forCmd colorPorts innerStep

def command : Code := sequence [
  push 63 false, getGroup, copy 38 55, innerMatrices,
  prepareOuter, matrix, emitMatrix, clear 40]

def program := compiled command 47 63

theorem groupPorts_injective : Function.Injective groupPorts := by decide
theorem splitPorts_injective : Function.Injective splitPorts := by decide
theorem outerPorts_injective : Function.Injective outerPorts := by decide

end SubexponentialSAT.Subexp.GlobalBasisProgram

end OAI.Algorithms
