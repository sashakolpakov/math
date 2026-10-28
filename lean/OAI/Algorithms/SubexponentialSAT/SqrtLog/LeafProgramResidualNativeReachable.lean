import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeReachableNode
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeRun

namespace OAI.Algorithms

/-! Actual residual execution using only reachable assignment frame facts. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls LeafNodeSamplesProgram
open SubexpLiftRing MomentsAssembly
noncomputable section

 theorem command_correct_reachable
    (c : NodeArithmetic) (sources : ℕ → NodeNative.HeadInputs)
    (relation : (i : ℕ) → AssignmentContext → List Bool →
      Contribution (sources i).n (baseWidth 3 c.t) c.d → Prop)
    (validFrame : ℕ → (Fin 768 → List Bool) → Prop)
    (Valid : (Fin 768 → List Bool) → Prop) (nodes : ℕ → List Bool)
    (H X Y A Wnode cost : ℕ → ℕ) (Q : ℕ)
    (assignment : ∀ i,Relational.AssignmentContract 3 c.t c.modulus c.cache c.table c.u c.J
      (relation i) Factor.assignment c.degree c.width Finset.univ (validFrame i) (A i))
    (inputs : ∀ i < Q,∀ regs store,Valid store.frame →
      store.index=List.replicate i true → store.node=nodes i → store.jet=[] → store.shape=[] →
      NodeInput c (sources i) (state regs (maskStore store)))
    (bounds : ∀ i < Q,∀ regs store,Valid store.frame →
      store.index=List.replicate i true → store.node=nodes i → store.jet=[] → store.shape=[] →
      ∀ b (pr : NodeNative.Preparation (sources i) (state regs (maskStore store)) b),
        NodePostReachable c pr (validFrame i) (H i) (X i) (Y i) (A i) (Wnode i) (cost i))
    (a : Data) (words : List (List Bool)) (h W C count width : ℕ)
    (hcounter : a.stacks 330=ProgramEncoding.encodeRecords words)
    (hhigh : ∀ i∈LeafHighContextProgram.changed,a.stacks i=[])
    (hshape : words.map List.length=List.replicate h 1)
    (hcard : h=HighIncidenceProgram.Restriction.highCount (a.stacks 338))
    (hwidth : ∀ i,(a.stacks i).length ≤ W)
    (h190 : a.stacks 190=[]) (h191 : a.stacks 191=[]) (h265 : a.stacks 265=[])
    (h699 : a.stacks 699=[]) (hprep : ∀ i∈Count.Prepare.ports,a.stacks i=[])
    (hnodes : ((List.finRange Q).map (fun i => nodes i.val)).flatten=a.stacks 256)
    (hvalid : ∀ rh,Valid (Samples.prepared (LeafHighContextProgram.finished a rh words.flatten)).stacks)
    (hblank : ∀ rh i,i∈collectorBlankPorts →
      (Samples.prepared (LeafHighContextProgram.finished a rh words.flatten)).stacks i=[])
    (hsource : ∀ rh,(Samples.prepared (LeafHighContextProgram.finished a rh words.flatten)).stacks 300=
      Encoding.encodeList id (records (Rel.nodeSamples nodes) 0 Q))
    (hrecovery : ∀ rh (entries : (i : Fin Q) → NodeWitness c (sources i.val) (relation i.val)),
      (∀ i,(entries i).good Valid nodes i.val ∧
        (entries i).encode.length ≤ c.J*(c.d*baseWidth 3 c.t)) →
      ∀ rr,∃ r : Recovery (sampled (LeafHighContextProgram.finished a rh words.flatten)
        nodes (fun i => (entries i).encode) rr),
        r.count=count ∧ r.cost ≤ C ∧
        ((countInput (sampled (LeafHighContextProgram.finished a rh words.flatten)
          nodes (fun i => (entries i).encode) rr)).stacks 194).length+
          baseWidth 3 r.t ≤ width) :
    ∃ time out, time ≤ residualBound W (highBound a h)
        (sampleBudget a nodes cost (c.J*(c.d*baseWidth 3 c.t)) Q) C ∧
      Eval Residual.command time a out ∧ BinaryArithmetic.toNat (out.stacks 323)=count ∧
      (out.stacks 323).length ≤ width ∧ out.stacks 324=[] ∧
      out.stacks=Function.update a.stacks 323 (out.stacks 323) ∧
      RegFrame a.regs out.regs := by
  exact run_of_contract Valid nodes (fun i => NodeWitness c (sources i) (relation i))
    (fun _ w => w.encode) (fun i w => w.good Valid nodes i) cost
    (c.J*(c.d*baseWidth 3 c.t)) Q
    (concrete_worker_reachable c sources relation validFrame Valid nodes H X Y A Wnode cost Q assignment inputs bounds)
    a words h W C count width hcounter hhigh hshape hcard hwidth h190 h191 h265 h699 hprep hnodes
    hvalid hblank hsource hrecovery

end
end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
