import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryAssembler
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ProgramTapeReplayMacros

/-! Actual node-cursor initialization and frame parsing never read or write
the external marked-record cursor320 or accumulated mass322. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeCursorReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

theorem native_init_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322) RingNodeSetup.initNodes :=
  ⟨avoids_clearProgram _ 301 0 1 (by decide),
    avoids_clearProgram _ 302 0 1 (by decide),
    avoids_clearProgram _ 305 0 1 (by decide),
    avoids_clearProgram _ 307 0 1 (by decide),
    avoids_clearProgram _ 78 0 1 (by decide),
    avoids_copyProgram _ 300 301 305 0 1 (by decide) (by decide) (by decide)⟩

theorem native_read_avoids :
    AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322) RingNodeSetup.readNode := by
  refine ⟨?_, avoids_record_reader _ SqrtLog.LeafNodeSamplesProgram.ports
    (by decide) (by decide), avoids_transferProgram _ 302 78 0 1 (by decide) (by decide)⟩
  change ¬ ((301 : Fin 768).val = 320 ∨ (301 : Fin 768).val = 322)
  decide

theorem call_avoids (command : Cmd 40 768)
    (hc : AvoidsCmd (fun i : Fin 768 => i.val = 320 ∨ i.val = 322) command) :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      (QueryAssembler.Nodes.call command) := by
  apply avoids_liftProgram
  exact avoids_compiled _ command hc 301 78

theorem initializeNodes_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      QueryAssembler.Nodes.initializeNodes := by
  refine ⟨call_avoids _ native_init_avoids, NodeFinishReplay.clearMany_avoids _ _ ?_⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide

theorem beginNode_avoids :
    AvoidsCmd (fun i : Fin 896 => i.val = 320 ∨ i.val = 322)
      QueryAssembler.Nodes.beginNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, call_avoids _ native_read_avoids⟩
  intro i hi
  simp only [QueryAssembler.Nodes.nodeResetPorts, List.mem_cons, List.mem_nil_iff,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeCursorReplay
