import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchFraming
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchInputCode
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchSearch
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchState
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchFinish
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchLoopCode
import OAI.Algorithms.SubexponentialSAT.Subexp.ConstraintMatrixProgram

namespace OAI.Algorithms

/-!
# Fixed outer local-basis construction

Each position/color iteration physically selects its Side list, counts that
list, constructs its constraint matrix, and executes the finite local-basis
search. Matrix construction and search use disjoint work banks. The emitted
records retain ascending position/color order and the actual chosen table.
-/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open BitProgram StructuredCalls

def matrixInputs : List (Fin 128 × Fin 128) :=
  [(112, 21), (113, 22), (114, 26), (108, 29), (109, 30), (110, 31),
   (111, 32), (117, 37), (118, 62), (115, 64)]

def buildMatrix : Code := .seq (copyMany matrixInputs)
  (.call (ProgramLinking.liftProgram ConstraintMatrixProgram.program matrixRegisters matrixPorts))

def colorBody : Code := .seq sideFilter
  (.seq dimensions (.seq buildMatrix (.seq runSearch finishSearch)))

def positionBody : Code := batchPositionBody colorBody

def command : Code := .seq makeWidth (batchCore colorBody)

def program := compiled command 107 127

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
