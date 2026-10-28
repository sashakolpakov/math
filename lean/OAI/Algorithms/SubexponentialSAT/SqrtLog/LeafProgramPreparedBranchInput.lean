import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedNodeArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyBranchFrame

namespace OAI.Algorithms

/-! Actual branch-loop control and accumulator tapes are immaterial to node
readiness. The invariant only fixes the static query and arithmetic masters. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
noncomputable section
variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Factor.Data} {hg : Guard (q.input k)}
    {W V L : ℕ} (p : Query.Preparation q k a hg W V L)

 theorem persistent_not_control (i : Fin 768) (hi : i∈persistentPorts) :
    i∉PreparedNodeReady.branchControlPorts := by
  simp only [persistentPorts,List.mem_cons,List.mem_nil_iff,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

 theorem query_collector_persistent_off_control
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : ∀i,i∉PreparedNodeReady.branchControlPorts →
      store.frame i=(PreparedNodeReady.branch p counter regs high).stacks i) :
    Persistent p.out (LeafNodeSamplesProgram.state rr store) := by
  intro i hi
  exact (persistent_collector store rr i hi).trans
    ((hf i (persistent_not_control i hi)).trans (query_branch_persistent p counter regs high i hi))

 theorem query_collector_input_off_control (hb : NodeNative.Blank a)
    (node : Fin (Query.packingProblem q k hg).Q)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : ∀i,i∉PreparedNodeReady.branchControlPorts →
      store.frame i=(PreparedNodeReady.branch p counter regs high).stacks i)
    (hn : store.index=List.replicate node.val true) (hs : store.shape=[]) (hj : store.jet=[]) :
    Residual.Native.NodeInput
      (nodeArithmetic q k p.lengths hg p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced)
      (heads q k hg p.firstWord p.remainingWords node) (LeafNodeSamplesProgram.state rr store) := by
  apply nodeInput_of_frame q k p.lengths hg p.modulus p.scalarCache p.half p.ringState
    p.arithmeticOutput.produced _ _
    (PreparedNodeReady.query_collector_ready_off_branchControl p hb node counter regs high rr store hf hn hs)
  · intro i hi
    have hm : LeafRingSetupProgram.wideStacks i∈persistentPorts := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hl : i.val < 340 := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (query_collector_persistent_off_control p counter regs high rr store hf _ hm).trans
      (p.arithmeticOutput.low i hl)
  · simpa [LeafNodeSamplesProgram.state,LeafNodeSamplesProgram.tapes] using hj

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
