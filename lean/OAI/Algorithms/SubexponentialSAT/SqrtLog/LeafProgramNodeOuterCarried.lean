import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeOuterCarriedBase
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopOuterCarried
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramFootprintOuterCarried

namespace OAI.Algorithms

/-! The concrete node program is independent of all three outer carried tapes. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay

attribute [local irreducible] Node.cleanup Node.cleanupPorts Node.clearList

/-- This certificate inspects the actual node stages, including all finite calls. -/
theorem node_command : AvoidsCmd hidden Node.command :=
by
  rw [Node.command]
  exact ⟨node_load_avoids,LeafHeadSetupProgram.FootprintOuterCarried.native_wide_avoids,
    node_cache_avoids,node_supports_avoids,denseCommand,node_cleanup_avoids⟩

theorem node_program : AvoidsProgram hidden Node.program :=
  avoids_compiled hidden Node.command node_command 78 102

/-- Replace the outer frame without adding an instruction or changing the result. -/
theorem node_eval_rebase {n : ℕ} {a b : Node.Data}
    (h : Eval Node.command n a b) (frame : Fin 768 → List Bool) :
    Eval Node.command n (rebaseState hidden frame a) (rebaseState hidden frame b) :=
  eval_rebase hidden node_command h frame

end SubexponentialSAT.SqrtLog.LeafProgram.OuterCarried

end OAI.Algorithms
