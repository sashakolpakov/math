import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramShift
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramCompare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgramSelectFrame
import OAI.Algorithms.SubexponentialSAT.ArithmeticCalls
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding

namespace OAI.Algorithms

/-! The finite table for sparse code rows. Runtime loops visit vertices,
local checks, and local ports only. The original clause count is used for a
binary comparison, never as the bound of a per-row scan. -/
namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 16 64

def low8 : Fin 8 → Fin 16 := Fin.castAdd 8
def low3 : Fin 3 → Fin 16 := Fin.castAdd 13

abbrev copy (src dst : Fin 64) : Cmd 16 64 :=
  .call (StackRoutines.copyProgram src dst 24 0 1)
abbrev clear (src : Fin 64) : Cmd 16 64 := .call (StackRoutines.clearProgram src 0 1)
abbrev push (dst : Fin 64) (b : Bool) : Cmd 16 64 := Subexp.TupleProgram.pushConst dst 0 b

def arithmeticWork : Fin 5 ↪ Fin 64 where
  toFun i := ⟨28+i.val,by omega⟩
  inj' := by intro i j h; apply Fin.ext; have hh := congrArg Fin.val h; dsimp at hh; omega

def arithmeticPorts (i : Fin 3) : ArithmeticCalls.Ports 64 where
  left := ![18,20,21] i
  right := ![3,14,22] i
  out := ![20,21,23] i
  work := arithmeticWork
  out_ne_left := by fin_cases i <;> decide
  out_ne_right := by fin_cases i <;> decide
  work_ne_left := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_right := by intro j; fin_cases i <;> fin_cases j <;> decide
  work_ne_out := by intro j; fin_cases i <;> fin_cases j <;> decide

abbrev liftArithmetic (c : Cmd 8 64) : Cmd 16 64 := liftCommand c 0 0 low8 id

abbrev indexArithmetic : Cmd 8 64 :=
  .seq (ArithmeticCalls.multiplyAt (arithmeticPorts 0))
    (ArithmeticCalls.addAt (arithmeticPorts 1))

def cellRegisters : Fin 4 → Fin 16 := ![0,1,8,9]
def cellStacks (_ : Fin 1) : Fin 64 := 0

abbrev readCoefficient : Cmd 16 64 :=
  .call (ProgramLinking.liftProgram Cell.program cellRegisters cellStacks)

def shiftStacks : Fin 4 → Fin 64 := ![1,17,19,18]
abbrev shiftVertex : Cmd 16 64 :=
  .seq (copy 2 17) (.seq (.base (.atom (.copy 7 12)))
    (.call (ProgramLinking.liftProgram Shift.program low8 shiftStacks)))

def compareStacks : Fin 8 → Fin 64 := ![21,4,33,34,35,36,37,38]
abbrev belowClauseCount : Cmd 16 64 :=
  .call (ProgramLinking.liftProgram Compare.program low8 compareStacks)

/-- Coefficients are 0, 1, or 2, with one-hot bits saved on registers8/9. -/
abbrev coefficientOffset : Cmd 16 64 :=
  .ite 9 (.seq (copy 4 22) (push 22 false))
    (.ite 8 (copy 4 22) (.base .skip))

def paddingStacks : Fin 3 → Fin 64 := ![25,23,13]
abbrev appendSlot : Cmd 16 64 :=
  .seq coefficientOffset
    (.seq (liftArithmetic (ArithmeticCalls.addAt (arithmeticPorts 2)))
      (.seq (copy 5 25)
        (.seq (.call (ProgramLinking.liftProgram ModularPrograms.paddingProgram low8 paddingStacks))
          (.seq (clear 23) (clear 22)))))

def incrementStacks (src : Fin 64) : Fin 2 → Fin 64 := ![src,41]
abbrev increment (src : Fin 64) : Cmd 16 64 :=
  .call (ProgramLinking.liftProgram (CounterPrograms.rippleProgram true) low3 (incrementStacks src))

abbrev preparePort : Cmd 16 64 :=
  .seq readCoefficient (.seq shiftVertex
    (.seq (liftArithmetic indexArithmetic) belowClauseCount))

abbrev finishPort : Cmd 16 64 :=
  .seq (.ite 7 appendSlot (.base .skip))
    (.seq (clear 18) (.seq (clear 20) (.seq (clear 21) (increment 14))))

abbrev portStep : Cmd 16 64 := .seq preparePort finishPort

def portLoop : UnaryForPrograms.Ports 16 64 := ⟨15,10,11⟩
def rowLoop : UnaryForPrograms.Ports 16 64 := ⟨16,10,11⟩
def vertexLoop : UnaryForPrograms.Ports 16 64 := ⟨8,14,15⟩

def frameStacks : Fin 2 → Fin 64 := ![13,12]
abbrev writeRow : Cmd 16 64 :=
  .seq (.call (ProgramLinking.liftProgram RowSelectionProgramSelect.frameProgram low3 frameStacks))
    (push 12 true)

abbrev rowStep : Cmd 16 64 :=
  .seq (copy 6 15) (.seq (copy 9 1)
    (.seq (UnaryForPrograms.forCmd portLoop portStep) (.seq (clear 14) writeRow)))

abbrev sideStep (side : Bool) : Cmd 16 64 :=
  .seq (.base (.atom (.set 12 side)))
    (.seq (copy 10 0) (.seq (copy 7 16) (UnaryForPrograms.forCmd rowLoop rowStep)))

abbrev vertexStep : Cmd 16 64 :=
  .seq (sideStep false) (.seq (sideStep true) (increment 2))

/-- The supplied unary r shape creates the initial zero vertex word. -/
def zeroVertexStacks : Fin 3 → Fin 64 := ![25,26,2]
abbrev initializeCommand : Cmd 16 64 :=
  .seq (push 12 false) (.seq (copy 11 25)
    (.call (ProgramLinking.liftProgram ModularPrograms.paddingProgram low8 zeroVertexStacks)))

abbrev command : Cmd 16 64 :=
  .seq initializeCommand (.seq (UnaryForPrograms.forCmd vertexLoop vertexStep) (clear 2))

def program := compiled command 10 12

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
