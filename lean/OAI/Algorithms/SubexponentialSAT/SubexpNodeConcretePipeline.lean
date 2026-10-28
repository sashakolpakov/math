import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpNodeWidePipeline
import OAI.Algorithms.SubexponentialSAT.SubexpNodeBlueprintStage

namespace OAI.Algorithms

/-!
# Fixed all-node program with the named physical producer stages

This closes the remaining finite-program parameter of the wider collector.
It does not assert the complete semantic NodeContract: that theorem also
needs the checked producer-format and readiness joins.
-/

namespace SubexponentialSAT.SubexpNodeConcretePipeline

open BitProgram StructuredCalls

def blueprint : SubexpNodeWideLoop.Stage := ⟨_, SubexpNodeBlueprintStage.program⟩
def worker := SubexpNodeWidePipeline.worker blueprint
def program := SubexpNodeWideLoop.program worker

end SubexponentialSAT.SubexpNodeConcretePipeline

end OAI.Algorithms
