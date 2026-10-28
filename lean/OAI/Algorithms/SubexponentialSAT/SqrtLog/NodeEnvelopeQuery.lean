import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeQueryPolynomial

namespace OAI.Algorithms

/-! Reachable storage for the actual addressed query, including its masked
factor references. The only size input is the pre-node physical local width. -/
noncomputable section
namespace SubexponentialSAT.SqrtLog.NodeEnvelope
open SubexponentialSAT BitProgram StructuredCalls MulticolorTypes SubexpSetupStorage
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram ProducedQueryResources
open LeafParametersProgram MomentsAssembly MomentsAssembly.Relational MomentsProgram

variable (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
  (hg : Guard (query.input k))
  (first : Word (problem query k hg).r (problem query k hg).Q)
  (tail : List (Word (problem query k hg).r (problem query k hg).Q))
  (node : Fin (problem query k hg).Q)

theorem query_assignment_storage {a b : NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) a b)
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) a)
    (input : ℕ) (hb : WordBound input a) {r Q : ℕ}
    (q : Factor.Spec r Q (Native.queryInputsAddressed query k hg first tail node).n
      (produce (query.input k)).d)
    (degree : List Bool)
    (ht : q.p.t=(produce (query.input k)).t)
    (hu : q.u=(produce (query.input k)).t)
    (hj : q.J=(produce (query.input k)).J)
    (hJ : a.stacks 243=List.replicate q.J true)
    (hcore : ∀ i : Fin 56,b.stacks (corePorts i)=
      Product.tapes (emptyCore (FactorLoop.assignmentEnvironment q degree)) i) :
    Reachable.BucketFrames (SubexpLiftRing.baseWidth 3 q.p.t) (produce (query.input k)).d
      (Finset.univ : Finset (Fin (Native.queryInputsAddressed query k hg first tail node).n)) q.u q.J
      (AssignmentStorage q degree (queryStorageCap query k occurrence qi hg first tail node input))
      b.stacks pr.supports pr.bucketInputs := by
  have hs := query_stream_bound query k occurrence qi hg first tail node pr ha input hb
  have hf := preparation_assignment_storage pr ha input _ hb q degree hJ hs hcore
  have hQr : (Native.queryInputsAddressed query k hg first tail node).Q*
      (Native.queryInputsAddressed query k hg first tail node).r=
      (problem query k hg).Q*(problem query k hg).r := rfl
  simpa only [queryStorageCap,ht,hu,hj,hQr] using hf

theorem masked_query_storage {a b : NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) (NodeNative.masked a) b)
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) (NodeNative.masked a))
    (input : ℕ) (hb : LocalWordBound input a) {r Q : ℕ}
    (q : Factor.Spec r Q (Native.queryInputsAddressed query k hg first tail node).n
      (produce (query.input k)).d)
    (degree : List Bool)
    (ht : q.p.t=(produce (query.input k)).t)
    (hu : q.u=(produce (query.input k)).t)
    (hj : q.J=(produce (query.input k)).J)
    (hJ : (NodeNative.masked a).stacks 243=List.replicate q.J true)
    (hcore : ∀ i : Fin 56,b.stacks (corePorts i)=
      Product.tapes (emptyCore (FactorLoop.assignmentEnvironment q degree)) i)
    (hv : query.Valid) (hn : 2 ≤ ambient query) (hsmall : SmallInputs query k (ambient query)) :
    Reachable.BucketFrames (SubexpLiftRing.baseWidth 3 q.p.t) (produce (query.input k)).d
      (Finset.univ : Finset (Fin (Native.queryInputsAddressed query k hg first tail node).n)) q.u q.J
      (AssignmentStorage q degree (queryStorageCap query k occurrence qi hg first tail node input))
      b.stacks pr.supports pr.bucketInputs ∧
    queryStorageCap query k occurrence qi hg first tail node input ≤
      2560000000000000000*(input+1)^8*
        ((resources query k occurrence qi hg first tail).bits+1)^8*
        (CostAssembly.assembledWork k (ambient query) (resources query k occurrence qi hg first tail)+1)^8 := by
  have hw := masked_wordBound a input hb
  exact ⟨query_assignment_storage query k occurrence qi hg first tail node pr ha input hw
    q degree ht hu hj hJ hcore,
    queryStorageCap_polynomial query k occurrence qi hg first tail node ha input hw hv hn hsmall⟩

end SubexponentialSAT.SqrtLog.NodeEnvelope

end

end OAI.Algorithms
