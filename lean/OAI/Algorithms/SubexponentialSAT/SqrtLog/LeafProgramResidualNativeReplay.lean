import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeMask
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeReplayBase

namespace OAI.Algorithms

/-! Replay the concrete node's bounded witness on arbitrary collector buffers. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls LeafNodeSamplesProgram
open MomentsAssembly SubexpLiftRing
noncomputable section

 theorem masked_state (regs : Fin 40 → Bool) (s : Store) :
    NodeNative.masked (state regs s)=state regs (maskStore s) := by
  apply congrArg (StructuredProgram.State.mk regs)
  funext i
  exact (maskStore_tapes s i).symm

 theorem replay_store (hcode : ProgramTapeReplay.AvoidsCmd NodeNative.collectorTape Node.command)
    (regs rr : Fin 40 → Bool) (s : Store) (bits : List Bool) (k : ℕ) (hs : s.shape=[])
    (he : Eval Node.command k (state regs (maskStore s))
      ⟨rr,Function.update (Function.update (tapes (maskStore s)) 78 []) 102 bits⟩) :
    Eval Node.command k (state regs s) (state rr {s with node:=[],jet:=bits,shape:=[]}) := by
  have he' : Eval Node.command k (NodeNative.masked (state regs s))
      ⟨rr,Function.update (Function.update (NodeNative.masked (state regs s)).stacks 78 []) 102 bits⟩ := by
    rw [masked_state]
    exact he
  have h := NodeNative.replay_with_footprint hcode (state regs s) rr bits k he'
  change Eval Node.command k (state regs s)
    ⟨rr,Function.update (Function.update (tapes s) 78 []) 102 bits⟩ at h
  rw [NodeNative.collector_output rr s bits hs] at h
  exact h

 theorem concrete_worker_masked_of_footprint
    (hcode : ProgramTapeReplay.AvoidsCmd NodeNative.collectorTape Node.command)
    (c : NodeArithmetic) (sources : ℕ → NodeNative.HeadInputs)
    (relation : (i : ℕ) → AssignmentContext → List Bool →
      Contribution (sources i).n (baseWidth 3 c.t) c.d → Prop)
    (validFrame : ℕ → (Fin 768 → List Bool) → Prop)
    (Valid : (Fin 768 → List Bool) → Prop) (nodes : ℕ → List Bool)
    (H X Y A W cost : ℕ → ℕ) (Q : ℕ)
    (assignment : ∀ i,Relational.AssignmentContract 3 c.t c.modulus c.cache c.table c.u c.J
      (relation i) Factor.assignment c.degree c.width Finset.univ (validFrame i) (A i))
    (inputs : ∀ i < Q,∀ regs store,Valid store.frame →
      store.index=List.replicate i true → store.node=nodes i → store.jet=[] → store.shape=[] →
      NodeInput c (sources i) (state regs (maskStore store)))
    (bounds : ∀ i < Q,∀ regs store,Valid store.frame →
      store.index=List.replicate i true → store.node=nodes i → store.jet=[] → store.shape=[] →
      ∀ b (pr : NodeNative.Preparation (sources i) (state regs (maskStore store)) b),
        NodePost c pr (validFrame i) (H i) (X i) (Y i) (A i) (W i) (cost i)) :
    Rel.WorkerContract Node.command Valid nodes
      (Rel.WitnessResult (fun i => NodeWitness c (sources i) (relation i))
        (fun _ w => w.encode) (fun i w => w.good Valid nodes i))
      cost (c.J*(c.d*baseWidth 3 c.t)) Q := by
  intro i hi regs store hv hx hn hj hs
  let inp := inputs i hi regs store hv hx hn hj hs
  obtain ⟨b,⟨pr⟩⟩ := NodeNative.prepare (sources i) (state regs (maskStore store)) inp.ready
  let post := bounds i hi regs store hv hx hn hj hs b pr
  obtain ⟨entries,hrel,hinv,k,hk,rr,he,hr⟩ :=
    NodeNative.execute_of_assignment_contract (sources i) (state regs (maskStore store)) b pr inp.ready
      3 c.t c.modulus c.cache c.canonicalZero c.table c.degree c.width
      c.degreeLength c.widthLength c.u c.J c.positiveU c.positiveJ c.one c.zero
      inp.modulus inp.table inp.width inp.scalarZero inp.degree inp.precision inp.order inp.one inp.zero
      inp.output (relation i) (validFrame i) (H i) (X i) (Y i) (A i) (W i)
      (assignment i) post.size post.bytes post.valid post.workspace post.dictionary
  let w : NodeWitness c (sources i) (relation i) := ⟨regs,maskStore store,inp,b,pr,entries,hrel,hinv⟩
  refine ⟨w.encode,⟨w,⟨hv,hx,hn,hj,hs⟩,rfl⟩,?_,k,hk.trans post.paid,rr,?_,?_⟩
  · exact (MomentsReadoutProgram.outputBits_length 3 c.t c.modulus c.cache entries c.u c.zero 0 c.J).le
  · intro j hj _
    exact hr j hj
  · exact replay_store hcode regs rr store w.encode k hs he

end
end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
