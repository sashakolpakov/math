import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFixedSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchWidth
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeLocal

namespace OAI.Algorithms

/-! Fixed indexing and bounded collector frames for the nodes of one query. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing
noncomputable section
attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

def nodeIndex (_p : Query.Preparation q k initial hg W V L)
    (i : ℕ) : Fin (Query.packingProblem q k hg).Q :=
  ⟨i % (Query.packingProblem q k hg).Q,Nat.mod_lt _ (Query.packingProblem q k hg).hQ⟩

@[simp] theorem nodeIndex_fin (i : Fin (Query.packingProblem q k hg).Q) :
    nodeIndex p i.val=i := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt i.isLt

def nodeFamily (i : ℕ) : List Bool :=
  RingProgram.flat (RingNodeProgram.nodeCode ((numeric q k p.lengths).val 33)
    ((numeric q k p.lengths).val 34) (i+1))

def CollectorFrame (counter : List Bool) (rh : Fin 4 → Bool) (high : List Bool)
    (frame : Fin 768 → List Bool) : Prop :=
  (∀i,i∉PreparedNodeReady.branchControlPorts →
    frame i=(PreparedNodeReady.branch p counter rh high).stacks i) ∧
  ∀i,(frame i).length ≤ Query.Width.incomingWidth p

theorem collector_frame_initial (hw : ∀i,(initial.stacks i).length ≤ W)
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (words : List (List Bool))
    (hshape : words.map List.length=
      List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1)
    (hc : a.stacks 330=Encoding.encodeList id words)
    (h331 : a.stacks 331=[]) (h323 : a.stacks 323=[]) (h324 : a.stacks 324=[])
    (rh : Fin 4 → Bool) :
    CollectorFrame p (a.stacks 330) rh words.flatten
      (Samples.prepared (LeafHighContextProgram.finished
        (Residual.Native.outerReference a) rh words.flatten)).stacks :=
  ⟨invariant_collector_frame p a ha rh words.flatten,
    invariant_sampler_width p hw a ha words hshape hc h331 h323 h324 rh⟩

theorem collector_local_width (hw : ∀i,(initial.stacks i).length ≤ W)
    (counter : List Bool) (rh : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : CollectorFrame p counter rh high store.frame)
    (i : ℕ) (hi : i < (Query.packingProblem q k hg).Q)
    (hx : store.index=List.replicate i true) (hn : store.node=nodeFamily p i)
    (hj : store.jet=[]) (hs : store.shape=[]) :
    NodeNative.LocalWordBound (Query.Width.incomingWidth p) (LeafNodeSamplesProgram.state rr store) := by
  apply Residual.Native.collector_local_bound rr store i _ (nodeFamily p i)
    (fun j _=>hf.2 j) (Nat.le_trans hi.le (nodes_le_incoming p hw))
    (node_word_le_incoming p hw i) hx hn hj hs

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
