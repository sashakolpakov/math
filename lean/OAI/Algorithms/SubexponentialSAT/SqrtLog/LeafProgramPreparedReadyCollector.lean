import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFixedSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyConsumers
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchMetadata
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchInput

namespace OAI.Algorithms

/-! The actual collector's bounded reference supplies the complete source
and factor contracts. Only the genuine branch-frame invariant is required;
opaque carried tapes may have arbitrary length. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing SubexpSetupStorage
open LeafParametersProgram MulticolorTypes Subexp LayoutProgram PreparedSource
open NodeNative LeafHeadSetupProgram MomentsAssembly MomentsProgram MomentsAssembly.Relational
noncomputable section
attribute [local simp] Fin.coe_ofNat_eq_mod

variable {query : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (query.input k)} {W V L : ℕ}
    (p : Query.Preparation query k initial hg W V L)
    (occurrence qi : ℕ) (node : Fin (Query.packingProblem query k hg).Q)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store)
    (hframe : ∀i,i∉PreparedNodeReady.branchControlPorts →
      store.frame i=(PreparedNodeReady.branch p counter regs high).stacks i)
    (hhigh : high.length=HighIncidenceProgram.Restriction.highCount query.forward.reverse)
    (hindexNode : store.index=List.replicate node.val true) (hshape : store.shape=[])
    (hnode : store.node=RingProgram.flat (RingNodeProgram.nodeCode
      ((numeric query k p.lengths).val 33) ((numeric query k p.lengths).val 34) (node.val+1)))
    {b : NodeNative.Data}
    (pr : Preparation (heads query k hg p.firstWord p.remainingWords node)
      (LeafNodeSamplesProgram.state rr (Residual.Native.maskStore store)) b)
    (input : ℕ) (hinput : LocalWordBound input (LeafNodeSamplesProgram.state rr store))
    (hblank : NodeNative.Blank initial) (hr : query.Ready initial)
    (hv : query.Valid) (hindex : query.index=Encoding.encodeNat (markIndex query))
    (h728 : initial.stacks 728=[])
    (source : List (List (SAT.Literal (Fin (Query.packingProblem query k hg).n))))
    (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source)

local notation "q" => fixedSpec p hv source hsource node
local notation "A" => NodeEnvelope.queryStorageCap query k occurrence qi hg p.firstWord p.remainingWords node input

include pr hframe hhigh hindexNode hshape hnode hinput hblank hr hindex h728

 theorem collector_assignment_frames :
    Reachable.BucketFrames (baseWidth 3 (q).p.t) ((numeric query k p.lengths).val 34)
      Finset.univ (q).u (q).J
      (fun frame=>FactorLoop.AssignmentFrame q (List.replicate ((numeric query k p.lengths).val 34) true)
        (FactorResource.sourceCap q A A A) A A A LeafStatisticsProgram.Arity.decoded
        (q).p.ops.zeroRun.1 (q).p.ops.oneRun.1 query.forward
        (HighIncidenceProgram.Restriction.zeroMerge query.forward.reverse high).reverse (FactorLoop.maskedHigh frame))
      b.stacks pr.supports pr.bucketInputs := by
  have ha := PreparedNodeReady.query_collector_ready_off_branchControl p hblank node counter regs high
    rr (Residual.Native.maskStore store) hframe hindexNode hshape
  have hp := query_collector_persistent_off_control p counter regs high rr (Residual.Native.maskStore store) hframe
  have hm := collector_branch_metadata p counter regs high rr store hframe
  have h702 : b.stacks 702=query.forward :=
    (pr.frame 702 (by rw [Node.mem_cleanup]; norm_num)).trans hm.1
  have h703 : b.stacks 703=(HighIncidenceProgram.Restriction.zeroMerge query.forward.reverse high).reverse :=
    (pr.frame 703 (by rw [Node.mem_cleanup]; norm_num)).trans hm.2
  simpa only [h702,h703] using query_assignment_frames p occurrence qi node pr ha input
    (Residual.Native.maskStore_wordBound store rr input hinput) hr hp hv hindex h728
    (collector_node_word _ _ _ rr store hnode)
    (collector_branch_high_length p counter regs high hhigh rr store hframe) source hsource

 theorem collector_reference_input :
    FactorReady.Input q (FactorResource.sourceCap q A A A) A
      (assignmentBase q (List.replicate ((numeric query k p.lengths).val 34) true)
        (referenceHigh (Query.packingProblem query k hg).n b.stacks)) := by
  have ha := PreparedNodeReady.query_collector_ready_off_branchControl p hblank node counter regs high
    rr (Residual.Native.maskStore store) hframe hindexNode hshape
  have hp := query_collector_persistent_off_control p counter regs high rr (Residual.Native.maskStore store) hframe
  exact query_reference_input p occurrence qi node pr ha input
    (Residual.Native.maskStore_wordBound store rr input hinput) hr hp hv hindex h728
    (collector_node_word _ _ _ rr store hnode)
    (collector_branch_high_length p counter regs high hhigh rr store hframe) source hsource

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
