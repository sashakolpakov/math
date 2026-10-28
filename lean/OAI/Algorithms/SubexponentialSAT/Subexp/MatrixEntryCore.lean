import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixPaddingProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixPascalProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixWordSelectProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixSignedWordProgram

namespace OAI.Algorithms

/-! The fixed arithmetic workspace and subroutines of the joint-entry program. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

abbrev Data := State 9 37
abbrev Code := Cmd 9 37

def series : List Code → Code
  | [] => .base .skip
  | c :: cs => .seq c (series cs)

def lowRegisters : Fin 8 → Fin 9 := Fin.castAdd 1

abbrev callLow {s l : ℕ} (p : Program 8 s l) (hs : s ≤ 37) : Code :=
  .call (ProgramLinking.liftProgram p lowRegisters (Fin.castLE hs))

def copy (src dst : Fin 37) : Code := .call (copyProgram src dst 9 0 1)
def clear (src : Fin 37) : Code := .call (clearProgram src 0 1)
def transfer (src dst : Fin 37) : Code := .call (transferProgram src dst 0 1)
def move (src dst : Fin 37) : Code := .seq (transfer src 9) (transfer 9 dst)
def push (dst : Fin 37) : Code := TupleProgram.pushConst dst 0 true

def signedStacks : Fin 10 → Fin 37 := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 34]
def signedWord : Code := .call
  (ProgramLinking.liftProgram MatrixSignedWordProgram.program id signedStacks)

/-- On a compatible joint entry the first pop removes the nonfixed unchanged
anchor. Positivity of that count is an explicit premise proved in refinement. -/
def prepare : Code := series [
  .base (.atom (.pop 2 0 1)),
  move 2 35,
  copy 35 34,
  move 3 36,
  copy 33 16,
  push 16,
  copy 29 5,
  copy 30 14,
  copy 31 12,
  copy 32 17]

def coefficientStage : Code := series [
  callLow MatrixPaddingProgram.program (by decide),
  copy 36 16,
  callLow MatrixPascalProgram.program (by decide)]

def finishEntry : Code := series [
  copy 30 10,
  copy 30 10,
  push 10,
  copy 35 15,
  callLow MatrixWordSelectProgram.program (by decide),
  signedWord]

def calculate : Code := .seq coefficientStage finishEntry

def positive : Code := .seq prepare calculate

def cleanupPorts : List (Fin 37) := [2, 3, 5, 10, 12, 13, 14, 15, 16, 17, 34, 35, 36]

def cleanup : Code := .seq (series (cleanupPorts.map clear)) (.seq (copy 33 22) (clear 33))

def input (regs : Fin 9 → Bool)
    (colorWidth positions left right index rowWidth modulus zero coefficients count : List Bool) : Data :=
  ⟨regs, fun j =>
    if j = 21 then colorWidth else if j = 22 then positions
    else if j = 23 then left else if j = 24 then right
    else if j = 25 then index else if j = 26 then rowWidth
    else if j = 29 then modulus else if j = 30 then zero
    else if j = 31 then coefficients else if j = 32 then count else []⟩

def output (base : Data) (regs : Fin 9 → Bool) (answer : List Bool) : Data :=
  ⟨regs, Function.update base.stacks 0 answer⟩

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
