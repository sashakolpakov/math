import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PreparedNodeReadyBranch

namespace OAI.Algorithms

/-! Closed physical readiness from the executed query record. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram LeafHeadSetupProgram
variable {q : LeafQueryFrontend.Query} {k : ℕ} {a : Data} {hg : Guard (q.input k)}
  {W V L : ℕ} (p : Query.Preparation q k a hg W V L)

theorem query_blank (hb : NodeNative.Blank a) :
    NodeNative.Blank (Marked.Wide.maskCopied (Query.prepared p.out)) :=
  prepared_blank_of_low p hb p.arithmeticOutput.lowBlank

theorem branch_blank (hb : NodeNative.Blank a)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool) :
    NodeNative.Blank (branch p counter regs high) :=
  branch_blank_of_low p hb p.arithmeticOutput.lowBlank counter regs high

/-- The collector may carry arbitrary stream buffers. Only its actual frame,
index, and empty shape are read by this physical readiness theorem. -/
theorem query_collector_ready (hb : NodeNative.Blank a)
    (node : Fin (Query.packingProblem q k hg).Q)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : store.frame=(branch p counter regs high).stacks)
    (hn : store.index=unary node.val) (hs : store.shape=[]) :
    NodeNative.Ready (Native.queryInputsAddressed q k hg p.firstWord p.remainingWords node)
      (LeafNodeSamplesProgram.state rr store) :=
  collector_ready_of_low p hb p.arithmeticOutput.lowBlank node counter regs high rr store hf hn hs
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodeReady

end

end OAI.Algorithms
