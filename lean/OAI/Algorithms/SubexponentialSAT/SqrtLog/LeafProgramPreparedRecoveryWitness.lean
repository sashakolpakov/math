import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedRecoveryQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFixedSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedBranchCountQuery

namespace OAI.Algorithms

/-! Concrete typed node witnesses give the residual recovery certificate.
All ring inputs and encoded jets come from the actual preparation and sampled
state; the certificate exposes its fixed count, native cost and output width. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedRecovery
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing SubexpQuarticRing
open Residual.Native MomentsAssembly NodeConcrete LeafNodeSamplesProgram
set_option quotPrecheck false
noncomputable section
attribute [local irreducible] Execute.guardedModel

variable {q : LeafQueryFrontend.Query} {k : ℕ} {initial : Factor.Data}
    {hg : Guard (q.input k)} {W V L : ℕ} (p : Query.Preparation q k initial hg W V L)
local notation "num" => PreparedSource.numeric q k p.lengths
local notation "t" => (num).val 33
local notation "d" => (num).val 34
local notation "Q" => (Query.packingProblem q k hg).Q
local notation "J" => (produce (q.input k)).J
local notation "ctx" => PreparedSource.nodeArithmetic q k p.lengths hg p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced
local notation "heads" => LeafHeadSetupProgram.Native.queryInputsAddressed q k hg p.firstWord p.remainingWords

 theorem producedCount_eq (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (i : Fin Q) {a b : Factor.Data} (pr : NodeNative.Preparation (heads i) a b) :
    sourceHashes (producedSpec p hv source hs i pr)=sourceHashes (PreparedSource.fixedSpec p hv source hs i) ∧
    (producedSpec p hv source hs i pr).marked=(PreparedSource.fixedSpec p hv source hs i).marked ∧
    (producedSpec p hv source hs i pr).markedClause=(PreparedSource.fixedSpec p hv source hs i).markedClause :=
  ⟨rfl,rfl,rfl⟩

 def fixedHighCount (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (base : Fin Q) (high : List Bool) : ℕ :=
  let spec := PreparedSource.fixedSpec p hv source hs base
  NodeSemantics.ternaryFixedHighCount (planHigh (Query.packingProblem q k hg))
    (fun v => (HighIncidenceProgram.Restriction.zeroMerge q.forward.reverse high).reverse.getD v.val.val false)
    (sourceHashes spec) spec.marked spec.markedClause

 theorem fixedHighCount_eq_rank (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (base : Fin Q) (words : List (List Bool))
    (hshape : words.map List.length=List.replicate
      (HighIncidenceProgram.Branches.trueCount q.forward.reverse) 1) :
    fixedHighCount p hv source hs base words.flatten=
      PreparedBranchCount.rankValue (planHigh (Query.packingProblem q k hg))
        (sourceHashes (PreparedSource.fixedSpec p hv source hs base))
        (PreparedSource.fixedSpec p hv source hs base).marked
        (PreparedSource.fixedSpec p hv source hs base).markedClause
        (CounterPrograms.value words.flatten) :=
  PreparedBranchCount.query_physical_count q k hg _ _ _ words hshape

 def nativeCost : ℕ :=
  Count.recoveryBudget Q J t d p.modulus.bits (p.ringState.stacks 202)

 def countWidth : ℕ := p.modulus.bits.length+baseWidth 3 t

 def outerFixedHighCount (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (a : Factor.Data) (high : List Bool) (base : Fin Q) : ℕ :=
  let spec := PreparedSource.fixedSpec p hv source hs base
  NodeSemantics.ternaryFixedHighCount (planHigh (Query.packingProblem q k hg))
    (fun v => (HighIncidenceProgram.Restriction.zeroMerge
      ((outerReference a).stacks 338) high).reverse.getD v.val.val false)
    (sourceHashes spec) spec.marked spec.markedClause

 theorem producedCountValue_eq (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (a : Factor.Data) (high : List Bool) (base : Fin Q)
    {na nb : Factor.Data} (pr : NodeNative.Preparation (heads base) na nb) :
    NodeSemantics.ternaryFixedHighCount (planHigh (Query.packingProblem q k hg))
      (fun v => (HighIncidenceProgram.Restriction.zeroMerge
        ((outerReference a).stacks 338) high).reverse.getD v.val.val false)
      (sourceHashes (producedSpec p hv source hs base pr))
      (producedSpec p hv source hs base pr).marked
      (producedSpec p hv source hs base pr).markedClause=
    outerFixedHighCount p hv source hs a high base := by
  unfold outerFixedHighCount
  obtain ⟨hhash,hmark,hclause⟩ := producedCount_eq p hv source hs base pr
  exact (congrArg (fun hashes => NodeSemantics.ternaryFixedHighCount
    (planHigh (Query.packingProblem q k hg))
    (fun v => (HighIncidenceProgram.Restriction.zeroMerge
      ((outerReference a).stacks 338) high).reverse.getD v.val.val false)
    hashes (producedSpec p hv source hs base pr).marked
      (producedSpec p hv source hs base pr).markedClause) hhash).trans
    ((congrArg (fun mark => NodeSemantics.ternaryFixedHighCount
      (planHigh (Query.packingProblem q k hg))
      (fun v => (HighIncidenceProgram.Restriction.zeroMerge
        ((outerReference a).stacks 338) high).reverse.getD v.val.val false)
      (sourceHashes (PreparedSource.fixedSpec p hv source hs base)) mark
        (producedSpec p hv source hs base pr).markedClause) hmark).trans
      (congrArg (fun clause => NodeSemantics.ternaryFixedHighCount
        (planHigh (Query.packingProblem q k hg))
        (fun v => (HighIncidenceProgram.Restriction.zeroMerge
          ((outerReference a).stacks 338) high).reverse.getD v.val.val false)
        (sourceHashes (PreparedSource.fixedSpec p hv source hs base))
        (PreparedSource.fixedSpec p hv source hs base).marked clause) hclause))

 theorem outerFixedHighCount_eq_fixed (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (a : Factor.Data) (high : List Bool) (base : Fin Q)
    (hm : (outerReference a).stacks 338=q.forward.reverse) :
    outerFixedHighCount p hv source hs a high base=fixedHighCount p hv source hs base high := by
  unfold outerFixedHighCount fixedHighCount
  rw [hm]

 structure RecoveryBundle (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (high : List Bool) where
  na : Fin Q → Factor.Data
  nb : Fin Q → Factor.Data
  preparation : ∀ i,NodeNative.Preparation (heads i) (na i) (nb i)
  input : ∀ i,NodeInput ctx (heads i) (na i)
  entries : Fin Q → List (MomentsProgram.Product.Entry
    (Query.packingProblem q k hg).n (baseWidth 3 t) d)
  buckets : ∀ i,Relational.BucketsRel 3 t p.modulus p.scalarCache
    (ctx).table t J
    (AssignmentConcrete.relation (PreparedSource.fixedSpec p hv source hs i) q.forward
      (HighIncidenceProgram.Restriction.zeroMerge q.forward.reverse high).reverse
      LeafStatisticsProgram.Arity.decoded (ctx).zero (ctx).one)
    (preparation i).supports (NodeNative.originEntries (ctx).one)
    (preparation i).bucketInputs [] (entries i)
  encoded : Fin Q → List Bool
  encoded_eq : encoded=(fun i => MomentsReadoutProgram.outputBits 3 t p.modulus
    p.scalarCache (entries i) t (ctx).zero 0 J)

 def witnessBundle (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (high : List Bool)
    (ws : (i : Fin Q) → NodeWitness ctx (heads i)
      (PreparedSource.fixedRelation p hv source hs i high (ctx).zero (ctx).one)) :
    RecoveryBundle p hv source hs high where
  na := fun i => state (ws i).regs (ws i).store
  nb := fun i => (ws i).prepared
  preparation := fun i => (ws i).preparation
  input := fun i => (ws i).input
  entries := fun i => (ws i).entries
  buckets := fun i => (ws i).buckets
  encoded := fun i => (ws i).encode
  encoded_eq := rfl

 def bundleProducedCount (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (a : Factor.Data) (high : List Bool)
    (bundle : RecoveryBundle p hv source hs high) (base : Fin Q) : ℕ :=
  NodeSemantics.ternaryFixedHighCount (planHigh (Query.packingProblem q k hg))
    (fun v => (HighIncidenceProgram.Restriction.zeroMerge
      ((outerReference a).stacks 338) high).reverse.getD v.val.val false)
    (sourceHashes (producedSpec p hv source hs base (bundle.preparation base)))
    (producedSpec p hv source hs base (bundle.preparation base)).marked
    (producedSpec p hv source hs base (bundle.preparation base)).markedClause

 theorem bundleProducedCount_eq_fixed (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (a : Factor.Data) (ha : Residual.Branch.Invariant
      (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (high : List Bool) (bundle : RecoveryBundle p hv source hs high) (base : Fin Q) :
    bundleProducedCount p hv source hs a high bundle base=
      fixedHighCount p hv source hs base high :=
  (producedCountValue_eq p hv source hs a high base (bundle.preparation base)).trans
    (outerFixedHighCount_eq_fixed p hv source hs a high base
      ((outerReference_visible a 338 (by decide)).trans (PreparedSource.invariant_mask p a ha)))

 opaque rawRecovery (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hwidth : ∀ clause∈source,clause.length ≤ k)
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (rh : Fin 4 → Bool) (high : List Bool) (rr : Fin 40 → Bool)
    (bundle : RecoveryBundle p hv source hs high)
    (base : Fin Q) :
    {r : Recovery (sampled (LeafHighContextProgram.finished (outerReference a) rh high)
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1)))
      bundle.encoded rr) //
      r.t=t ∧ r.d=d ∧ r.Q=Q ∧ r.J=J ∧
      r.count=bundleProducedCount p hv source hs a high bundle base} := by
  rw [bundle.encoded_eq]
  exact queryRecovery
    (q:=q) (k:=k) (initial:=initial) (hg:=hg) (W:=W) (V:=V) (L:=L)
    p hv source hs hwidth a ha rh high rr
    bundle.na bundle.nb bundle.preparation bundle.input bundle.entries bundle.buckets base

 opaque fixedRecovery (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hwidth : ∀ clause∈source,clause.length ≤ k)
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (rh : Fin 4 → Bool) (high : List Bool) (rr : Fin 40 → Bool)
    (bundle : RecoveryBundle p hv source hs high)
    (base : Fin Q) :
    {r : Recovery (sampled (LeafHighContextProgram.finished (outerReference a) rh high)
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1)))
      bundle.encoded rr) //
      r.t=t ∧ r.d=d ∧ r.Q=Q ∧ r.J=J ∧
      r.count=fixedHighCount p hv source hs base high ∧
      (countInput (sampled (LeafHighContextProgram.finished (outerReference a) rh high)
        (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1))) bundle.encoded rr)).stacks 194=
        p.modulus.bits ∧
      (countInput (sampled (LeafHighContextProgram.finished (outerReference a) rh high)
        (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1))) bundle.encoded rr)).stacks 202=
        p.ringState.stacks 202} := by
  let rc := rawRecovery
    (q:=q) (k:=k) (initial:=initial) (hg:=hg) (W:=W) (V:=V) (L:=L)
    p hv source hs hwidth a ha rh high rr bundle base
  have hf := sampled_ringFrame p a ha rh high
    (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1))) bundle.encoded rr
  have h194 := (count_ringFrame hf 194 (by simp [ringPorts])).trans
    p.arithmeticOutput.produced.caches.modulus
  have h202 := count_ringFrame hf 202 (by simp [ringPorts])
  exact ⟨rc.1,rc.2.1,rc.2.2.1,rc.2.2.2.1,rc.2.2.2.2.1,
    rc.2.2.2.2.2.trans (bundleProducedCount_eq_fixed p hv source hs a ha high bundle base),
    h194,h202⟩

 theorem sampled_recovery_words (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (rh : Fin 4 → Bool) (high : List Bool) (encoded : Fin Q → List Bool)
    (rr : Fin 40 → Bool) :
    (countInput (sampled (LeafHighContextProgram.finished (outerReference a) rh high)
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1))) encoded rr)).stacks 194=
        p.modulus.bits ∧
    (countInput (sampled (LeafHighContextProgram.finished (outerReference a) rh high)
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1))) encoded rr)).stacks 202=
        p.ringState.stacks 202 := by
  have hf := sampled_ringFrame p a ha rh high
    (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1))) encoded rr
  exact ⟨(count_ringFrame hf 194 (by simp [ringPorts])).trans
      p.arithmeticOutput.produced.caches.modulus,
    count_ringFrame hf 202 (by simp [ringPorts])⟩

 theorem recovery_cost_eq_native {input : Factor.Data} (r : Recovery input)
    (hrt : r.t=t) (hrd : r.d=d) (hrQ : r.Q=Q) (hrJ : r.J=J)
    (h194 : (countInput input).stacks 194=p.modulus.bits)
    (h202 : (countInput input).stacks 202=p.ringState.stacks 202) :
    r.cost=nativeCost p := by
  unfold Recovery.cost nativeCost
  rw [hrQ,hrJ,hrt,hrd,h194,h202]

 theorem recovery_width_eq {input : Factor.Data} (r : Recovery input)
    (hrt : r.t=t) (h194 : (countInput input).stacks 194=p.modulus.bits) :
    ((countInput input).stacks 194).length+baseWidth 3 r.t=countWidth p := by
  rw [hrt,h194]
  rfl

 theorem witnesses_recovery (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hwidth : ∀ clause∈source,clause.length ≤ k)
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (rh : Fin 4 → Bool) (high : List Bool) (rr : Fin 40 → Bool)
    (ws : (i : Fin Q) → NodeWitness ctx (heads i)
      (PreparedSource.fixedRelation p hv source hs i high (ctx).zero (ctx).one))
    (base : Fin Q) :
    ∃ r : Recovery (sampled (LeafHighContextProgram.finished (outerReference a) rh high)
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1)))
      (fun i => (ws i).encode) rr),
      r.count=fixedHighCount p hv source hs base high ∧ r.cost=nativeCost p ∧
      ((countInput (sampled (LeafHighContextProgram.finished (outerReference a) rh high)
        (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1)))
        (fun i => (ws i).encode) rr)).stacks 194).length+baseWidth 3 r.t=countWidth p := by
  let bundle := witnessBundle p hv source hs high ws
  let rc := fixedRecovery
    (q:=q) (k:=k) (initial:=initial) (hg:=hg) (W:=W) (V:=V) (L:=L)
    p hv source hs hwidth a ha rh high rr bundle base
  let r := rc.1
  have hrt := rc.2.1
  have hrd := rc.2.2.1
  have hrQ := rc.2.2.2.1
  have hrJ := rc.2.2.2.2.1
  have hrcount := rc.2.2.2.2.2.1
  have h194 := rc.2.2.2.2.2.2.1
  have h202 := rc.2.2.2.2.2.2.2
  refine ⟨r,?_,?_,?_⟩
  · exact hrcount
  · exact recovery_cost_eq_native
      (q:=q) (k:=k) (initial:=initial) (hg:=hg) (W:=W) (V:=V) (L:=L)
      p r hrt hrd hrQ hrJ h194 h202
  · exact recovery_width_eq
      (q:=q) (k:=k) (initial:=initial) (hg:=hg) (W:=W) (V:=V) (L:=L)
      p r hrt h194

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedRecovery

end OAI.Algorithms
