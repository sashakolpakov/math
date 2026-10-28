import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryWidthPrepare
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendSemantics

namespace OAI.Algorithms

/-! Exact high-assignment metadata and node words at the actual collector
boundary. The original ambient coordinate order is retained. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing
attribute [local simp] Fin.coe_ofNat_eq_mod
noncomputable section
variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)

 theorem query_mask :
    (Marked.Wide.maskCopied (Query.prepared p.out)).stacks 338=q.forward.reverse := by
  rw [Marked.Wide.maskCopied_frame _ 338 (by decide),Query.Width.prepared_mask,
    Query.Width.output_mask]
  simp only [LeafQueryFrontend.Query.forward,List.reverse_reverse]

 theorem branch_mask (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool) :
    (PreparedNodeReady.branch p counter regs high).stacks 702=q.forward := by
  rw [PreparedNodeReady.branch,LeafHighContextProgram.finished_mask]
  simp only [Function.update_of_ne (by decide : (338 : Fin 768)≠330)]
  rw [query_mask,List.reverse_reverse]

 theorem branch_high (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool) :
    (PreparedNodeReady.branch p counter regs high).stacks 703=
      (HighIncidenceProgram.Restriction.zeroMerge q.forward.reverse high).reverse := by
  rw [PreparedNodeReady.branch,LeafHighContextProgram.finished_high]
  simp only [Function.update_of_ne (by decide : (338 : Fin 768)≠330)]
  rw [query_mask]

 theorem branch_high_length (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (hh : high.length=HighIncidenceProgram.Restriction.highCount q.forward.reverse) :
    ((PreparedNodeReady.branch p counter regs high).stacks 703).length=
      (Query.packingProblem q k hg).n := by
  rw [branch_high,List.length_reverse,(HighIncidenceProgram.Restriction.zeroMerge_spec _ _ hh).1,
    List.length_reverse,LeafQueryFrontend.Query.forward_length]
  rfl

 theorem invariant_mask (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a) :
    a.stacks 338=q.forward.reverse :=
  (ha.2 338 (by decide)).trans (query_mask p)

 theorem collector_branch_metadata (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : ∀i,i∉PreparedNodeReady.branchControlPorts →
      store.frame i=(PreparedNodeReady.branch p counter regs high).stacks i) :
    (LeafNodeSamplesProgram.state rr (Residual.Native.maskStore store)).stacks 702=q.forward ∧
    (LeafNodeSamplesProgram.state rr (Residual.Native.maskStore store)).stacks 703=
      (HighIncidenceProgram.Restriction.zeroMerge q.forward.reverse high).reverse := by
  constructor
  · change store.frame 702=q.forward
    exact (hf 702 (by decide)).trans (branch_mask p counter regs high)
  · change store.frame 703=_
    exact (hf 703 (by decide)).trans (branch_high p counter regs high)

 theorem collector_branch_high_length (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (hh : high.length=HighIncidenceProgram.Restriction.highCount q.forward.reverse)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hf : ∀i,i∉PreparedNodeReady.branchControlPorts →
      store.frame i=(PreparedNodeReady.branch p counter regs high).stacks i) :
    ((LeafNodeSamplesProgram.state rr (Residual.Native.maskStore store)).stacks 703).length=
      (Query.packingProblem q k hg).n := by
  change (store.frame 703).length=_
  rw [hf 703 (by decide)]
  exact branch_high_length p counter regs high hh

 theorem collector_node_word (t d i : ℕ) (rr : Fin 40 → Bool)
    (store : LeafNodeSamplesProgram.Store)
    (hn : store.node=RingProgram.flat (RingNodeProgram.nodeCode t d (i+1))) :
    (LeafNodeSamplesProgram.state rr (Residual.Native.maskStore store)).stacks 78=
      RingProgram.flat (RingNodeProgram.nodeCode t d (i+1)) := hn

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
