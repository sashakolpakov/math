import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryCore
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanProgram

namespace OAI.Algorithms

/-! The complete fixed control table for a joint-matrix entry.
All numerical parameters are runtime data. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

def scanStage : Code := series [
  copy 22 33,
  callLow MatrixInputProgram.program (by decide),
  callLow MatrixScanProgram.program (by decide)]

def command : Code := .seq scanStage (.seq (.ite 7 positive (copy 30 0)) cleanup)

def program := compiled command 23 0

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
