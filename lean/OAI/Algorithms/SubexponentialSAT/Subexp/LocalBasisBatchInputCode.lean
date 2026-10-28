import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchStorage
import OAI.Algorithms.SubexponentialSAT.Subexp.TypeFiberProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixDimensions
import OAI.Algorithms.SubexponentialSAT.Subexp.BlockCopyProgram

namespace OAI.Algorithms

/-! Fixed port assignments and commands for constructing the width, Side
records, and counted dimensions used by the local-basis batch. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls

def fiberRegisters : Fin 8 → Fin 32 := Fin.castAdd 24
def fiberPorts : Fin 16 → Fin 128 :=
  ![107, 0, 1, 2, 3, 4, 5, 6, 7, 8, 53, 112, 117, 118, 114, 9]
def dimensionRegisters : Fin 5 → Fin 32 := Fin.castAdd 27
def dimensionPorts : Fin 7 → Fin 128 := ![53, 0, 1, 123, 124, 2, 3]
def widthRegisters : Fin 3 → Fin 32 := Fin.castAdd 29
def widthPorts : Fin 4 → Fin 128 := ![112, 114, 0, 124]

theorem fiberRegisters_injective : Function.Injective fiberRegisters := Fin.castAdd_injective _ _
theorem fiberPorts_injective : Function.Injective fiberPorts := by decide
theorem dimensionRegisters_injective : Function.Injective dimensionRegisters := Fin.castAdd_injective _ _
theorem dimensionPorts_injective : Function.Injective dimensionPorts := by decide
theorem widthRegisters_injective : Function.Injective widthRegisters := Fin.castAdd_injective _ _
theorem widthPorts_injective : Function.Injective widthPorts := by decide

def makeWidth : Code := .seq (copy 113 124)
  (.seq (.base (.atom (.set 2 false)))
    (.call (ProgramLinking.liftProgram BlockCopyProgram.program widthRegisters widthPorts)))

def sideFilter : Code := .call
  (ProgramLinking.liftProgram (TypeFiberProgram.program false) fiberRegisters fiberPorts)

def dimensions : Code := .call
  (ProgramLinking.liftProgram ConstraintMatrixDimensions.program dimensionRegisters dimensionPorts)

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
