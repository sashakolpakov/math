import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.LocalBasisBatchFraming
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! Fixed instructions for the two outer local-basis loops. Runtime counts,
contexts, output records, and cost bounds are not parameters of the code. -/

namespace SubexponentialSAT.Subexp.LocalBasisBatchProgram

open StructuredCalls

def colorLoopPorts : UnaryForPrograms.Ports 32 128 := ⟨120, 28, 29⟩
def positionLoopPorts : UnaryForPrograms.Ports 32 128 := ⟨119, 30, 31⟩

def finishColorList : Code := .seq (TupleProgram.pushConst 122 0 false)
  (.seq (transfer 122 126) (appendRecord 126 121))

def batchPositionBody (body : Code) : Code := .seq (copy 112 120)
  (.seq (UnaryForPrograms.forCmd colorLoopPorts body)
    (.seq finishColorList (.seq (clear 118) (TupleProgram.pushConst 117 0 true))))

def batchCore (body : Code) : Code := .seq (copy 113 119)
  (.seq (UnaryForPrograms.forCmd positionLoopPorts (batchPositionBody body))
    (.seq (TupleProgram.pushConst 121 0 false)
      (.seq (transfer 121 127) (clear 117))))

end SubexponentialSAT.Subexp.LocalBasisBatchProgram

end OAI.Algorithms
