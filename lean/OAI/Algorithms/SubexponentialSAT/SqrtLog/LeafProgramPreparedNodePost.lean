import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedNodePostTransport
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyCollector
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramQueryCostNode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeQueryCaps

namespace OAI.Algorithms

/-! The actual collector supplies the node postcondition, including a fixed
polynomial cost. No numerical size or callback correctness oracle is assumed. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodePost
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpSetupStorage
open LeafParametersProgram MulticolorTypes PreparedSource PreparedReady
open NodeNative LeafHeadSetupProgram MomentsAssembly
attribute [local irreducible] Execute.guardedModel

theorem collector_nodePost : ∀
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
        Query.Cost.nodeInputExponent Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent) := by
  intro query k initial hg W V L p occurrence qi node counter regs high rr store
    hframe hhigh hindexNode hshape hjet hnode b pr hinput hblank hr hv hn hs hindex h728 source hsource
  dsimp only
  let c := nodeArithmetic query k p.lengths hg p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced
  have hinp := query_collector_input_off_control p hblank node counter regs high rr
    (Residual.Native.maskStore store) hframe hindexNode hshape hjet
  have hb := Residual.Native.maskStore_wordBound store rr (Query.Width.incomingWidth p) hinput
  have hJ : (LeafNodeSamplesProgram.state rr (Residual.Native.maskStore store)).stacks 243=
      List.replicate (produce (query.input k)).J true := hinp.order
  obtain ⟨hsize,hbytes,hworkspace,hdict,_,_⟩ :=
    NodeEnvelope.query_execution_caps query k occurrence qi hg p.firstWord p.remainingWords node
      pr hinp.ready (Query.Width.incomingWidth p) hb hJ
  have hframes := collector_assignment_frames p occurrence qi node counter regs high rr store
    hframe hhigh hindexNode hshape hnode pr (Query.Width.incomingWidth p) hinput hblank hr hv
    hindex h728 source hsource
  have hp := query_collector_persistent_off_control p counter regs high rr
    (Residual.Native.maskStore store) hframe
  have htime := Query.Cost.selected_native_node_bound p occurrence qi node pr hinp.ready (Query.Width.incomingWidth p) hb hr hp
    hv hn hs hindex h728 (collector_node_word _ _ _ rr store hnode)
    (collector_branch_high_length p counter regs high hhigh rr store hframe) source hsource
  have htp : (fixedSpec p hv source hsource node).p.t=(numeric query k p.lengths).val 33 :=
    native_spec_precision (heads query k hg p.firstWord p.remainingWords node)
      (numeric query k p.lengths) (Query.ring_precision_pos (query.input k) p.lengths hg)
      (Query.ring_degree_pos (query.input k) p.lengths hg)
      (cacheWords _) (cacheWords_correct _) p.modulus p.scalarCache p.half p.ringState
      p.arithmeticOutput.produced (numeric_field query k p.lengths hg) query hv _
      (produce_J_pos (query.input k)) source hsource
  have hparams := fixedSpec_parameters p hv source hsource node
  have hfr := reachable_parameters
    (n:=(Query.packingProblem query k hg).n)
    (B:=baseWidth 3 (fixedSpec p hv source hsource node).p.t)
    (B':=baseWidth 3 ((numeric query k p.lengths).val 33))
    (d:=(numeric query k p.lengths).val 34)
    (u:=(fixedSpec p hv source hsource node).u) (u':=(numeric query k p.lengths).val 33)
    (J:=(fixedSpec p hv source hsource node).J) (J':=(produce (query.input k)).J)
    Finset.univ (collectorFrame p occurrence qi hv source hsource node high)
    b.stacks pr.supports pr.bucketInputs
    (congrArg (baseWidth 3) htp) hparams.1 hparams.2.1 hframes
  refine ⟨hsize,hbytes,?_,hworkspace,?_,?_⟩
  · exact hfr
  · have ht : c.t=(produce (query.input k)).t := numeric_t query k p.lengths hg
    have hd : c.d=(produce (query.input k)).d := numeric_d query k p.lengths hg
    have hu : c.u=(produce (query.input k)).t := numeric_t query k p.lengths hg
    change dictionaryByteEnvelope (baseWidth 3 c.t) c.d
      (ProducedQueryResources.ambient query+c.u+c.J)
      (dictionaryCapacity (Finset.univ : Finset (Fin (ProducedQueryResources.ambient query))) c.u c.J) ≤ _
    rw [ht,hd,hu]
    exact hdict
  · exact budget_parameters
      (B:=baseWidth 3 (fixedSpec p hv source hsource node).p.t)
      (B':=baseWidth 3 ((numeric query k p.lengths).val 33))
      (u:=(fixedSpec p hv source hsource node).u) (u':=(numeric query k p.lengths).val 33)
      (J:=(fixedSpec p hv source hsource node).J) (J':=(produce (query.input k)).J)
      pr (congrArg (baseWidth 3) htp) hparams.1 hparams.2.1 htime

end SubexponentialSAT.SqrtLog.LeafProgram.PreparedNodePost

end

end OAI.Algorithms
