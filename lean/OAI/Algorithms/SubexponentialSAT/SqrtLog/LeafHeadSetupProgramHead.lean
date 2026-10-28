import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramMatrix
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramTuples
import OAI.Algorithms.SubexponentialSAT.UnaryForPrograms

namespace OAI.Algorithms

/-! Fixed one-head iteration and unary loop, independent of node cache bootstrapping. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadSetupProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpSetupStorage

def matrixInputs : List (Fin 768 × Fin 288) :=
  [(141,0),(650,17),(128,18),(651,23),
   (135,225),(136,226),(640,227),(641,228),(140,229),(642,230),
   (138,231),(139,232),(130,233),(131,234),(307,235),(132,236),(647,281)]
def matrixOutputs : List (Fin 288 × Fin 768) := [(21,669)]

abbrev matrixBuckets (entry : Cmd 16 256) : Code :=
  stage (Matrix.program entry) id (by decide) matrixInputs matrixOutputs

theorem matrixInputs_protected : ∀ p∈matrixInputs,Protected p.1 := by simp [matrixInputs,Protected,temporary]
theorem matrixOutputs_protected : ∀ p∈matrixOutputs,Protected p.2 := by simp [matrixOutputs,Protected,temporary]

def clearHead : Code := clearMany [650,651,652,669,670,671]
def advanceAddress : Code := SubexponentialSAT.Subexp.TupleProgram.pushConst 649 0 true

abbrev headStep (entry : Cmd 16 256) : Code :=
  .seq prepareHead (.seq (matrixBuckets entry)
    (.seq appendHead (.seq clearHead advanceAddress)))

abbrev headLoop (entry : Cmd 16 256) : Code :=
  UnaryForPrograms.forCmd ⟨648,0,1⟩ (headStep entry)

end SubexponentialSAT.SqrtLog.LeafHeadSetupProgram

end OAI.Algorithms
