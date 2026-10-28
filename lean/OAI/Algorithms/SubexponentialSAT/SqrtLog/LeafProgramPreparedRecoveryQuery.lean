import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedRecoveryFrame
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedFixedSpec
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcretePreparedJets
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramNodeConcretePreparedDegree

namespace OAI.Algorithms

/-! The recovery certificate is instantiated from an executed query, actual
per-node preparations and their relational sparse output witnesses. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedRecovery
open SubexponentialSAT BitProgram StructuredCalls LeafParametersProgram SubexpLiftRing SubexpQuarticRing
open Residual.Native MomentsAssembly NodeConcrete
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
local notation "ht" => Query.ring_precision_pos (q.input k) p.lengths hg
local notation "hd" => Query.ring_degree_pos (q.input k) p.lengths hg
local notation "ops" => RingProgram.modelRing t ht hd (IrreducibleSearch.data hd) p.modulus p.scalarCache
local notation "ctx" => PreparedSource.nodeArithmetic q k p.lengths hg p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced
local notation "heads" => LeafHeadSetupProgram.Native.queryInputsAddressed q k hg p.firstWord p.remainingWords

 def producedSpec (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (i : Fin Q) {a b : Factor.Data} (pr : NodeNative.Preparation (heads i) a b) :=
  PreparedSource.nativeSpecOfInputs (heads i) num ht hd pr.head.words pr.head.cache
    p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced
    (PreparedSource.numeric_field q k p.lengths hg) q hv J (produce_J_pos (q.input k)) source hs

 theorem producedSpec_eq (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (i : Fin Q) {a b : Factor.Data} (pr : NodeNative.Preparation (heads i) a b) :
    producedSpec p hv source hs i pr=PreparedSource.fixedSpec p hv source hs i := by
  have hw := PreparedSource.cacheWords_eq (heads i) pr.head.cache
  unfold producedSpec PreparedSource.fixedSpec PreparedSource.nativeSpec
  simp only [hw]

 theorem producedRelation_eq (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (i : Fin Q) {a b : Factor.Data} (pr : NodeNative.Preparation (heads i) a b)
    (bits : List Bool) :
    AssignmentConcrete.relation (producedSpec p hv source hs i pr) q.forward bits
      LeafStatisticsProgram.Arity.decoded (ctx).zero (ctx).one =
    AssignmentConcrete.relation (PreparedSource.fixedSpec p hv source hs i) q.forward bits
      LeafStatisticsProgram.Arity.decoded (ctx).zero (ctx).one := by rfl

 opaque queryRecovery (hv : q.Valid)
    (source : List (List (SAT.Literal (Fin (Query.packingProblem q k hg).n))))
    (hs : q.clauses=HashInputProgram.Expansion.encodedClauses source)
    (hwidth : ∀ clause∈source,clause.length ≤ k)
    (a : Factor.Data)
    (ha : Residual.Branch.Invariant (Marked.Wide.maskCopied (Query.prepared p.out)) a)
    (rh : Fin 4 → Bool) (high : List Bool) (rr : Fin 40 → Bool)
    (na nb : Fin Q → Factor.Data)
    (pr : ∀ i,NodeNative.Preparation (heads i) (na i) (nb i))
    (hin : ∀ i,NodeInput ctx (heads i) (na i))
    (entries : Fin Q → List (MomentsProgram.Product.Entry (Query.packingProblem q k hg).n (baseWidth 3 t) d))
    (hr : ∀ i,Relational.BucketsRel 3 t p.modulus p.scalarCache
      (ctx).table t J
      (AssignmentConcrete.relation (PreparedSource.fixedSpec p hv source hs i) q.forward
        (HighIncidenceProgram.Restriction.zeroMerge q.forward.reverse high).reverse
        LeafStatisticsProgram.Arity.decoded (ctx).zero (ctx).one)
      (pr i).supports (NodeNative.originEntries (ctx).one) (pr i).bucketInputs [] (entries i))
    (base : Fin Q) :
    {r : Recovery (sampled (LeafHighContextProgram.finished (outerReference a) rh high)
      (fun i => RingProgram.flat (RingNodeProgram.nodeCode t d (i+1)))
      (fun i => MomentsReadoutProgram.outputBits 3 t p.modulus p.scalarCache (entries i) t (ctx).zero 0 J) rr) //
      r.t=t ∧ r.d=d ∧ r.Q=Q ∧ r.J=J ∧
      r.count=NodeSemantics.ternaryFixedHighCount (planHigh (Query.packingProblem q k hg))
        (fun v => (HighIncidenceProgram.Restriction.zeroMerge
          ((outerReference a).stacks 338) high).reverse.getD v.val.val false)
        (sourceHashes (producedSpec p hv source hs base (pr base)))
        (producedSpec p hv source hs base (pr base)).marked
        (producedSpec p hv source hs base (pr base)).markedClause} := by
  let bits := (HighIncidenceProgram.Restriction.zeroMerge ((outerReference a).stacks 338) high).reverse
  let H := planHigh (Query.packingProblem q k hg)
  let highValue : H → Bool := fun v => bits.getD v.val.val false
  let spec := producedSpec p hv source hs base (pr base)
  let target := specTarget spec H highValue
  let count := NodeSemantics.ternaryFixedHighCount H highValue (sourceHashes spec) spec.marked spec.markedClause
  have hm : (outerReference a).stacks 338=q.forward.reverse :=
    (outerReference_visible a 338 (by decide)).trans (PreparedSource.invariant_mask p a ha)
  have hr' : ∀ i,Relational.BucketsRel 3 t p.modulus p.scalarCache
      (ctx).table t J
      (AssignmentConcrete.relation (producedSpec p hv source hs i (pr i)) q.forward
        (HighIncidenceProgram.Restriction.zeroMerge ((outerReference a).stacks 338) high).reverse
        LeafStatisticsProgram.Arity.decoded (ctx).zero (ctx).one)
      (pr i).supports (NodeNative.originEntries (ctx).one) (pr i).bucketInputs [] (entries i) := by
    intro i
    apply Relational.BucketsRel.mono (h := hr i)
    intro c x v h
    have h' : AssignmentConcrete.relation (PreparedSource.fixedSpec p hv source hs i) q.forward
        (HighIncidenceProgram.Restriction.zeroMerge ((outerReference a).stacks 338) high).reverse
        LeafStatisticsProgram.Arity.decoded (ctx).zero (ctx).one c x v := by
      simpa only [hm] using h
    have heq := congrFun (congrFun (congrFun
      (producedRelation_eq p hv source hs i (pr i)
        (HighIncidenceProgram.Restriction.zeroMerge ((outerReference a).stacks 338) high).reverse)
      c) x) v
    exact heq.mpr h'
  have hhas := query_prepared_hasJets q hv k hg p.firstWord p.remainingWords na nb pr
    (fun i => (hin i).ready) num ht hd p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced
    (PreparedSource.numeric_field q k p.lengths hg) J (produce_J_pos (q.input k))
    (fun i => by rw [(hin i).order,List.length_replicate]; rfl)
    source hs bits (ctx).zero (ctx).one (ops).zero_correct (ops).one_correct entries hr' base
  have hdegree : target.natDegree < Q*J :=
    query_prepared_degree q hv k hg p.firstWord p.remainingWords base p.lengths
      (pr base).head.words (pr base).head.cache p.modulus p.scalarCache p.half p.ringState
      p.arithmeticOutput.produced source hs hwidth H highValue
  have hm : 1 ≤ (q.input k).clauses := hg.2.2.1
  have hcount : count ≤ (q.input k).clauses*2^(Query.packingProblem q k hg).n :=
    specTarget_count_bound spec H highValue (q.input k).clauses hm
  have hlarge : (q.input k).clauses*2^(Query.packingProblem q k hg).n < 3^t := by
    rw [PreparedSource.numeric_t q k p.lengths hg]
    exact precision_sufficient (q.input k).ambient (q.input k).clauses
  have hconstant : target.eval 0=(count : (IrreducibleSearch.data hd).O t) :=
    specTarget_count spec (PreparedSource.generatedCode p.arithmeticOutput.produced).modulus
      (PreparedSource.generatedCode p.arithmeticOutput.produced).cache
      (PreparedSource.generatedCode p.arithmeticOutput.produced).half rfl
      (PreparedSource.generatedCode p.arithmeticOutput.produced).inverse H highValue
  apply ofProduced num ht hd p.modulus p.scalarCache p.half p.ringState p.arithmeticOutput.produced
    _ (sampled_ringFrame p a ha rh high _ _ rr) Q J (Query.packingProblem q k hg).hQ
    (produce_J_pos (q.input k)) (PreparedSource.numeric_J q k p.lengths hg)
    (PreparedSource.numeric_field q k p.lengths hg) (Query.ring_exponent (q.input k) p.lengths hg)
    (fun i => readoutJet 3 t p.modulus p.scalarCache (entries i) t (ctx).zero J)
    _ _ target hdegree hhas count (q.input k).clauses (Query.packingProblem q k hg).n hcount hlarge hconstant
  · rw [sampled_nodes]
    rfl
  · exact sampled_readout_jets 3 t p.modulus p.scalarCache entries t J (ctx).zero _ _ rr

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedRecovery

end OAI.Algorithms
