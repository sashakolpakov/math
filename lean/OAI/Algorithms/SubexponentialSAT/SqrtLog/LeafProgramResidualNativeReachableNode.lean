import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeReplay
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeReachable
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeReplay

namespace OAI.Algorithms

/-! Reachable-frame node witnesses, replayed at the same time on the caller. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls LeafNodeSamplesProgram
open MomentsAssembly SubexpLiftRing
noncomputable section

structure NodePostReachable (c : NodeArithmetic) {s : NodeNative.HeadInputs} {a b : Data}
    (pr : NodeNative.Preparation s a b) (validFrame : (Fin 768 → List Bool) → Prop)
    (H X Y A W K : ℕ) : Prop where
  size : ∀ v∈pr.bucketInputs,BucketSize H X Y v
  bytes : (b.stacks 169).length ≤ H
  valid : Relational.Reachable.BucketFrames (baseWidth 3 c.t) c.d
    (Finset.univ : Finset (Fin s.n)) c.u c.J validFrame b.stacks pr.supports pr.bucketInputs
  workspace : ∀ i∈Node.cleanupPorts,(b.stacks i).length ≤ W
  dictionary : dictionaryByteEnvelope (baseWidth 3 c.t) c.d (s.n+c.u+c.J)
    (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) c.u c.J) ≤ W
  paid : NodeNative.fullBudget pr (baseWidth 3 c.t) c.d c.u c.J H X Y A W ≤ K

 theorem concrete_worker_reachable
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
        NodePostReachable c pr (validFrame i) (H i) (X i) (Y i) (A i) (W i) (cost i)) :
    Rel.WorkerContract Node.command Valid nodes
      (Rel.WitnessResult (fun i => NodeWitness c (sources i) (relation i))
        (fun _ w => w.encode) (fun i w => w.good Valid nodes i))
      cost (c.J*(c.d*baseWidth 3 c.t)) Q := by
  intro i hi regs store hv hx hn hj hs
  let inp := inputs i hi regs store hv hx hn hj hs
  obtain ⟨b,⟨pr⟩⟩ := NodeNative.prepare (sources i) (state regs (maskStore store)) inp.ready
  let post := bounds i hi regs store hv hx hn hj hs b pr
  obtain ⟨entries,hrel,hinv,k,hk,rr,he,hr⟩ :=
    NodeNative.execute_of_reachable_assignment_contract (sources i) (state regs (maskStore store)) b pr inp.ready
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
  · exact replay_store NodeNative.command_avoids regs rr store w.encode k hs he

end
end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
