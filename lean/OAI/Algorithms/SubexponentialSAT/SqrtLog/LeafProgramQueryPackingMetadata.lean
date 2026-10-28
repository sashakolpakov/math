import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryPackingRun

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram MulticolorTypes

/-- Port740 is the actual unary R consumed by the native denominator stage. -/
theorem packed_cutoff (x : Input) (l : Fin 8 → ℕ) (a b : Data)
    (p : PackingCallerProgram.Problem) (w : Word p.r p.Q) (tail : List (Word p.r p.Q))
    (he : PackingCallerProgram.Empty a)
    (hex : LeafQueryFrontend.Exported (Execute.guardedModel x l) a)
    (hb : b.stacks=(PackingCallerProgram.result a p w tail).stacks) :
    b.stacks 740=List.replicate (produce x).R true := by
  have hR : (Execute.guardedModel x l).val 29=(produce x).R :=
    (Execute.guardedModel_public x l 6).trans (Layout.model_core_values x l).2.2.2.2.2.2.1
  have hu : a.stacks 138=List.replicate (produce x).R true := by
    simpa [Exports.destination,Exports.unaryValues,hR] using hex.1 5
  rw [hb]
  have hp := PackingCallerProgram.result_parameter a p he w tail 10 (by decide) (by decide) (by decide)
  exact hp.trans hu

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
