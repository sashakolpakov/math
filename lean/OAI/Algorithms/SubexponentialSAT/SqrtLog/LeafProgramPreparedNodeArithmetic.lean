import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedPersistent
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyNative

namespace OAI.Algorithms

/-! The executed query's ring tapes reach every actual node invocation,
including the bounded reference used to replay arbitrary collector buffers. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram
attribute [local simp] Fin.coe_ofNat_eq_mod
noncomputable section
variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Factor.Data} {hg : Guard (q.input k)}
    {W V L : ℕ} (p : Query.Preparation q k a hg W V L)

 theorem query_branch_persistent (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool) :
    Persistent p.out (PreparedNodeReady.branch p counter regs high) :=
  ((persistent_prepared p.out).trans (persistent_maskCopied _)).trans
    ((persistent_counter _ counter).trans (persistent_highContext _ regs high))

 theorem query_collector_persistent (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : store.frame=(PreparedNodeReady.branch p counter regs high).stacks) :
    Persistent p.out (LeafNodeSamplesProgram.state rr store) := by
  intro i hi
  exact (persistent_collector store rr i hi).trans
    ((congrFun hf i).trans (query_branch_persistent p counter regs high i hi))

 theorem query_masked_collector_persistent (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : store.frame=(PreparedNodeReady.branch p counter regs high).stacks) :
    Persistent p.out (LeafNodeSamplesProgram.state rr (Residual.Native.maskStore store)) :=
  (query_collector_persistent p counter regs high rr store hf).trans (persistent_maskStore store rr)

 theorem query_collector_input (hb : NodeNative.Blank a)
    (node : Fin (Query.packingProblem q k hg).Q)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : store.frame=(PreparedNodeReady.branch p counter regs high).stacks)
    (hn : store.index=List.replicate node.val true) (hs : store.shape=[]) (hj : store.jet=[]) :
    Residual.Native.NodeInput
      (nodeArithmetic q k p.lengths hg p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced)
      (heads q k hg p.firstWord p.remainingWords node) (LeafNodeSamplesProgram.state rr store) := by
  apply nodeInput_of_frame q k p.lengths hg p.modulus p.scalarCache p.half p.ringState
    p.arithmeticOutput.produced _ _
    (PreparedNodeReady.query_collector_ready p hb node counter regs high rr store hf hn hs)
  · intro i hi
    have hm : LeafRingSetupProgram.wideStacks i∈persistentPorts := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    have hl : i.val < 340 := by
      simp only [List.mem_cons,List.mem_nil_iff,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (query_collector_persistent p counter regs high rr store hf _ hm).trans
      (p.arithmeticOutput.low i hl)
  · simpa [LeafNodeSamplesProgram.state,LeafNodeSamplesProgram.tapes] using hj

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
