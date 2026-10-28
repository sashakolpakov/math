import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeFootprint
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadSetupProgramFootprint
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramFactorLoopFramed

namespace OAI.Algorithms

/-! The entire actual node can be executed on one bounded reference store and
replayed at exactly the same cost with arbitrary collector buffers restored. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.NodeNative
open SubexponentialSAT BitProgram StructuredCalls ProgramTapeReplay
attribute [local irreducible] Node.command Node.cleanup Node.cleanupPorts Node.clearList

/-- Every concrete stage avoids even reading the seven collector buffers. -/
theorem command_avoids : AvoidsCmd collectorTape Node.command := by
  have hh : AvoidsCmd collectorTape Node.heads := LeafHeadSetupProgram.Footprint.native_wide_avoids
  have hm : AvoidsCmd collectorTape Node.moments := FactorLoop.dense_avoids
  rw [Node.command]
  exact ⟨load_avoids,hh,cache_avoids,supports_avoids,hm,cleanup_avoids⟩

theorem program_avoids : AvoidsProgram collectorTape Node.program :=
  avoids_compiled collectorTape Node.command command_avoids 78 102

/-- No execution or footprint premise beyond the actual bounded reference
execution: the original collector buffers and all other frame tapes survive. -/
theorem replay (a : Data) (rr : Fin 40 → Bool) (bits : List Bool) (k : ℕ)
    (h : Eval Node.command k (masked a)
      ⟨rr,Function.update (Function.update (masked a).stacks 78 []) 102 bits⟩) :
    Eval Node.command k a ⟨rr,Function.update (Function.update a.stacks 78 []) 102 bits⟩ :=
  replay_with_footprint command_avoids a rr bits k h

end SubexponentialSAT.SqrtLog.LeafProgram.NodeNative

end OAI.Algorithms
