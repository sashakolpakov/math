import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedRecoveryBound
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedIndex
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedResidualInput
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedNodeContract
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedNodePostModel
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostNode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedRecoveryWitness

namespace OAI.Algorithms

/-! Actual node execution and reconstruction for every physical high branch. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing MomentsAssembly
open Residual.Native LeafNodeSamplesProgram NodeNative LeafHeadSetupProgram PreparedNodePost
noncomputable section
attribute [local irreducible] Execute.guardedModel

theorem residual_run_core (post : ∀
    {query : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (query.input k)} {W V L : ℕ}
    (p : Query.Preparation query k initial hg W V L)
    (occurrence qi : ℕ) (node : Fin (Query.packingProblem query k hg).Q)
    (counter : List Bool) (regs : Fin 4 → Bool) (high : List Bool)
    (rr : Fin 40 → Bool) (store : LeafNodeSamplesProgram.Store),
    (∀ i,i∉PreparedNodeReady.branchControlPorts →
      store.frame i=(PreparedNodeReady.branch p counter regs high).stacks i) →
    high.length=HighIncidenceProgram.Restriction.highCount query.forward.reverse →
    store.index=List.replicate node.val true → store.shape=[] → store.jet=[] →
    store.node=RingProgram.flat (RingNodeProgram.nodeCode
      ((numeric query k p.lengths).val 33) ((numeric query k p.lengths).val 34) (node.val+1)) →
    ∀ {b : NodeNative.Data}
      (pr : Preparation (heads query k hg p.firstWord p.remainingWords node)
        (LeafNodeSamplesProgram.state rr (Residual.Native.maskStore store)) b),
    LocalWordBound (Query.Width.incomingWidth p) (LeafNodeSamplesProgram.state rr store) →
    NodeNative.Blank initial → query.Ready initial →
    ∀ (hv : query.Valid), 2 ≤ ProducedQueryResources.ambient query →
    ProducedQueryResources.SmallInputs query k (ProducedQueryResources.ambient query) →
    query.index=Encoding.encodeNat (markIndex query) → initial.stacks 728=[] →
    ∀ (source : List (List (SAT.Literal (Fin (Query.packingProblem query k hg).n))))
      (hsource : query.clauses=HashInputProgram.Expansion.encodedClauses source),
    let q := fixedSpec p hv source hsource node
    let A := storageCap p occurrence qi node
    Residual.Native.NodePostReachable
      (nodeArithmetic query k p.lengths hg p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced)
      pr (collectorFrame p occurrence qi hv source hsource node high)
      A A A (FactorResource.canonicalAssignmentCost q A) A
      (Query.Cost.nodeCap p occurrence qi Query.Cost.nodeCoefficient
        Query.Cost.nodeInputExponent Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent)) : ∀
    {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ}
    (p : Query.Preparation q k initial hg W V L) (occurrence qi : ℕ)
    (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source),
    (∀clause∈source,clause.length ≤ k) →
    (∀i,(initial.stacks i).length ≤ W) → NodeNative.Blank initial →
    (∀i,i∈entryBlankPorts → initial.stacks i=[]) →
    q.Ready initial → 2 ≤ ProducedQueryResources.ambient q →
    ProducedQueryResources.SmallInputs q k (ProducedQueryResources.ambient q) →
    q.index=Encoding.encodeNat (markIndex q) → initial.stacks 728=[] →
    ∀ (a : Factor.Data),
    Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a →
    ∀ (words : List (List Bool)),
    words.map List.length=List.replicate (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1 →
    a.stacks 330=Encoding.encodeList id words →
    a.stacks 331=[] → a.stacks 323=[] → a.stacks 324=[] →
    ∃ time out,
    time ≤ residualBound (Query.Width.incomingWidth p)
      (highBound a (HighIncidenceProgram.Branches.trueCount q.forward.reverse))
      (sampleBudget a (nodeFamily p) (fun _=>Query.Cost.nodeCap p occurrence qi Query.Cost.nodeCoefficient
          Query.Cost.nodeInputExponent Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent)
      ((produce (q.input k)).J*((numeric q k p.lengths).val 34*baseWidth 3 ((numeric q k p.lengths).val 33)))
      (Query.packingProblem q k hg).Q) (PreparedRecovery.nativeCost p) ∧
    Eval Residual.command time a out ∧
    BinaryArithmetic.toNat (out.stacks 323)=
      PreparedRecovery.fixedHighCount p hv source hs (nodeIndex p 0) words.flatten ∧
    (out.stacks 323).length ≤ PreparedRecovery.countWidth p ∧ out.stacks 324=[] ∧
    out.stacks=Function.update a.stacks 323 (out.stacks 323) ∧ RegFrame a.regs out.regs := by
  intro q k initial hg W V L p occurrence qi hv source hs hsource hw hb he hr hn hsmall hindex h728
    a ha words hshape hc h331 h323 h324
  let c := nodeArithmetic q k p.lengths hg p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced
  let src := fun i=>heads q k hg p.firstWord p.remainingWords (nodeIndex p i)
  let rel := fun i=>fixedRelation p hv source hs (nodeIndex p i) words.flatten c.zero c.one
  let vf := fun i=>PreparedNodePost.collectorFrame p occurrence qi hv source hs (nodeIndex p i) words.flatten
  let cap := fun i=>PreparedNodePost.storageCap p occurrence qi (nodeIndex p i)
  let assignmentCost := fun i=>FactorResource.canonicalAssignmentCost
    (fixedSpec p hv source hs (nodeIndex p i)) (cap i)
  let valid := CollectorFrame p (a.stacks 330)
  have hhigh := invariant_entry_empty p h728 he a ha
  have hclean := residual_count_empty p a ha h323 h324
  refine command_correct_outer c src rel vf
    (fun frame=>∃rh,valid rh words.flatten frame) (nodeFamily p)
    cap cap cap assignmentCost cap (fun _=>Query.Cost.nodeCap p occurrence qi Query.Cost.nodeCoefficient
          Query.Cost.nodeInputExponent Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent)
    (Query.packingProblem q k hg).Q ?_ ?_ ?_ a words
    (HighIncidenceProgram.Branches.trueCount q.forward.reverse) (Query.Width.incomingWidth p)
    (PreparedRecovery.nativeCost p)
    (PreparedRecovery.fixedHighCount p hv source hs (nodeIndex p 0) words.flatten)
    (PreparedRecovery.countWidth p) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i
    exact prepared_assignment_contract p hv source hs occurrence qi (nodeIndex p i) words.flatten h728
  · intro i hi regs store hvalid hx hxnode hj hsh
    obtain ⟨rh,hf⟩ := hvalid
    have hival : (nodeIndex p i).val=i := Nat.mod_eq_of_lt hi
    apply query_collector_input_off_control p hb (nodeIndex p i) (a.stacks 330) rh words.flatten
      regs (maskStore store) hf.1
    · simpa only [maskStore,hival] using hx
    · exact hsh
    · exact hj
  · intro i hi regs store hvalid hx hxnode hj hsh b pr
    obtain ⟨rh,hf⟩ := hvalid
    have hival : (nodeIndex p i).val=i := Nat.mod_eq_of_lt hi
    apply post p occurrence qi (nodeIndex p i) (a.stacks 330) rh words.flatten regs store hf.1
    · rw [List.length_flatten,hshape]
      simp [HighIncidenceProgram.Restriction.highCount,HighIncidenceProgram.Branches.trueCount]
    · simpa only [hival] using hx
    · exact hsh
    · exact hj
    · simpa only [hival,nodeFamily] using hxnode
    · exact collector_local_width p hw _ rh words.flatten regs store hf i hi hx hxnode hj hsh
    · exact hb
    · exact hr
    · exact hn
    · exact hsmall
    · exact hindex
    · exact h728
  · simpa only [outerReference_visible a 330 (by decide)] using hc
  · exact hhigh.1
  · exact hshape
  · rw [outerReference_visible a 338 (by decide),invariant_mask p a ha]
  · exact residual_input_width p hw a ha words hshape hc h331 h323 h324
  · exact hclean.1 190 (by decide)
  · exact hclean.1 191 (by decide)
  · exact residual_collector_empty p h728 he a ha
  · exact hclean.1 699 (by decide)
  · exact hclean.2
  · exact invariant_nodes p a ha
  · intro rh
    exact ⟨rh,collector_frame_initial p hw a ha words hshape hc h331 h323 h324 rh⟩
  · exact fun rh i hi=>hhigh.2 rh words.flatten i hi
  · exact fun rh=>invariant_node_source p a ha rh words.flatten
  · intro rh entries hentries rr
    let family := fun i : Fin (Query.packingProblem q k hg).Q => NodeWitness c
      (heads q k hg p.firstWord p.remainingWords i)
      (fixedRelation p hv source hs i words.flatten c.zero c.one)
    let observe := fun i (w : family i) => w.encode
    let ws : ∀i,family i := fun i=>transportFamily family (nodeIndex_fin p i) (entries i)
    have henc : (fun i=>(ws i).encode)=(fun i=>(entries i).encode) := by
      funext i
      exact observe_transport family observe (nodeIndex_fin p i) (entries i)
    have hrec := PreparedRecovery.witnesses_recovery p hv source hs hsource a ha
      rh words.flatten rr ws (nodeIndex p 0)
    rw [henc] at hrec
    exact recovery_weaken hrec

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedSource

end OAI.Algorithms
