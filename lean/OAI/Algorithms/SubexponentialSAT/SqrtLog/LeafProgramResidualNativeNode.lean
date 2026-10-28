import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramResidualNativeJets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeNativeDense

namespace OAI.Algorithms

/-! A relational witness of an actual concrete node run. Only physical
readiness, subordinate assignment correctness and numerical bounds are inputs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native
open SubexponentialSAT BitProgram StructuredCalls LeafNodeSamplesProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram MomentsAssembly
noncomputable section

structure NodeArithmetic where
  t : ℕ
  d : ℕ
  u : ℕ
  J : ℕ
  modulus : SubexpPreparedQuartic.Modulus 3 t
  cache : RingProgram.ScalarCache 3 t
  canonicalZero : BinaryArithmetic.toNat cache.zero.val < 3^t
  table : Fin d → Fin d → Fin d → Word (baseWidth 3 t)
  degree : List Bool
  width : List Bool
  degreeLength : degree.length=d
  widthLength : width.length=baseWidth 3 t
  positiveU : 0 < u
  positiveJ : 0 < J
  one : RingProgram.Code (Word (baseWidth 3 t)) d
  zero : RingProgram.Code (Word (baseWidth 3 t)) d

structure NodeInput (c : NodeArithmetic) (s : NodeNative.HeadInputs) (a : Data) : Prop where
  ready : NodeNative.Ready s a
  modulus : a.stacks 194=c.modulus.bits
  table : a.stacks 201=RingTriple.tableEncoding c.table
  width : a.stacks 202=c.width
  scalarZero : a.stacks 203=c.cache.zero.val
  degree : a.stacks 204=c.degree
  precision : a.stacks 212=List.replicate c.u true
  order : a.stacks 243=List.replicate c.J true
  one : a.stacks 207=RingProgram.flat c.one
  zero : a.stacks 280=RingProgram.flat c.zero
  output : a.stacks 102=[]

structure NodePost (c : NodeArithmetic) {s : NodeNative.HeadInputs} {a b : Data}
    (pr : NodeNative.Preparation s a b) (validFrame : (Fin 768 → List Bool) → Prop)
    (H X Y A W K : ℕ) : Prop where
  size : ∀ v∈pr.bucketInputs,BucketSize H X Y v
  bytes : (b.stacks 169).length ≤ H
  valid : BucketFrames (n:=s.n) validFrame b.stacks pr.bucketInputs
  workspace : ∀ i∈Node.cleanupPorts,(b.stacks i).length ≤ W
  dictionary : dictionaryByteEnvelope (baseWidth 3 c.t) c.d (s.n+c.u+c.J)
    (dictionaryCapacity (Finset.univ : Finset (Fin s.n)) c.u c.J) ≤ W
  paid : NodeNative.fullBudget pr (baseWidth 3 c.t) c.d c.u c.J H X Y A W ≤ K

structure NodeWitness (c : NodeArithmetic) (s : NodeNative.HeadInputs)
    (relation : AssignmentContext → List Bool → Contribution s.n (baseWidth 3 c.t) c.d → Prop) where
  regs : Fin 40 → Bool
  store : Store
  input : NodeInput c s (state regs store)
  prepared : Data
  preparation : NodeNative.Preparation s (state regs store) prepared
  entries : List (Product.Entry s.n (baseWidth 3 c.t) c.d)
  buckets : Relational.BucketsRel 3 c.t c.modulus c.cache c.table c.u c.J relation
    preparation.supports (NodeNative.originEntries c.one) preparation.bucketInputs [] entries
  invariant : EntryInvariant Finset.univ c.u c.J entries

 def NodeWitness.encode {c : NodeArithmetic} {s : NodeNative.HeadInputs}
    {relation : AssignmentContext → List Bool → Contribution s.n (baseWidth 3 c.t) c.d → Prop}
    (w : NodeWitness c s relation) : List Bool :=
  MomentsReadoutProgram.outputBits 3 c.t c.modulus c.cache w.entries c.u c.zero 0 c.J

 def NodeWitness.good {c : NodeArithmetic} {s : NodeNative.HeadInputs}
    {relation : AssignmentContext → List Bool → Contribution s.n (baseWidth 3 c.t) c.d → Prop}
    (Valid : (Fin 768 → List Bool) → Prop) (nodes : ℕ → List Bool) (i : ℕ)
    (w : NodeWitness c s relation) : Prop :=
  Valid w.store.frame ∧ w.store.index=List.replicate i true ∧
    w.store.node=nodes i ∧ w.store.jet=[] ∧ w.store.shape=[]

 theorem concrete_worker (c : NodeArithmetic) (sources : ℕ → NodeNative.HeadInputs)
    (relation : (i : ℕ) → AssignmentContext → List Bool →
      Contribution (sources i).n (baseWidth 3 c.t) c.d → Prop)
    (validFrame : ℕ → (Fin 768 → List Bool) → Prop)
    (Valid : (Fin 768 → List Bool) → Prop) (nodes : ℕ → List Bool)
    (H X Y A W cost : ℕ → ℕ) (Q : ℕ)
    (assignment : ∀ i,Relational.AssignmentContract 3 c.t c.modulus c.cache c.table c.u c.J
      (relation i) Factor.assignment c.degree c.width Finset.univ (validFrame i) (A i))
    (inputs : ∀ i < Q,∀ regs store,Valid store.frame →
      store.index=List.replicate i true → store.node=nodes i → store.jet=[] → store.shape=[] →
      NodeInput c (sources i) (state regs store))
    (bounds : ∀ i < Q,∀ regs store,Valid store.frame →
      store.index=List.replicate i true → store.node=nodes i → store.jet=[] → store.shape=[] →
      ∀ b (pr : NodeNative.Preparation (sources i) (state regs store) b),
        NodePost c pr (validFrame i) (H i) (X i) (Y i) (A i) (W i) (cost i)) :
    Rel.WorkerContract Node.command Valid nodes
      (Rel.WitnessResult (fun i => NodeWitness c (sources i) (relation i))
        (fun _ w => w.encode) (fun i w => w.good Valid nodes i))
      cost (c.J*(c.d*baseWidth 3 c.t)) Q := by
  intro i hi regs store hv hx hn hj hs
  let inp := inputs i hi regs store hv hx hn hj hs
  obtain ⟨b,⟨pr⟩⟩ := NodeNative.prepare (sources i) (state regs store) inp.ready
  let post := bounds i hi regs store hv hx hn hj hs b pr
  obtain ⟨entries,hrel,hinv,k,hk,rr,he,hr⟩ :=
    NodeNative.execute_of_assignment_contract (sources i) (state regs store) b pr inp.ready
      3 c.t c.modulus c.cache c.canonicalZero c.table c.degree c.width
      c.degreeLength c.widthLength c.u c.J c.positiveU c.positiveJ c.one c.zero
      inp.modulus inp.table inp.width inp.scalarZero inp.degree inp.precision inp.order inp.one inp.zero
      inp.output (relation i) (validFrame i) (H i) (X i) (Y i) (A i) (W i)
      (assignment i) post.size post.bytes post.valid post.workspace post.dictionary
  let w : NodeWitness c (sources i) (relation i) := ⟨regs,store,inp,b,pr,entries,hrel,hinv⟩
  refine ⟨w.encode,⟨w,⟨hv,hx,hn,hj,hs⟩,rfl⟩,?_,k,hk.trans post.paid,rr,?_,?_⟩
  · exact (MomentsReadoutProgram.outputBits_length 3 c.t c.modulus c.cache entries c.u c.zero 0 c.J).le
  · intro j hj _
    exact hr j hj
  · change Eval Node.command k (state regs store)
      ⟨rr,Function.update (Function.update (tapes store) 78 []) 102 w.encode⟩ at he
    rw [NodeNative.collector_output rr store w.encode hs] at he
    exact he

end
end SubexponentialSAT.SqrtLog.LeafProgram.Residual.Native

end OAI.Algorithms
