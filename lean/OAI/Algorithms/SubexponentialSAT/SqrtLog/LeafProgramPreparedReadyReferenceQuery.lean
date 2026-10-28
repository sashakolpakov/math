import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyReference

namespace OAI.Algorithms

/-! The synthetic reference uses exactly the uniform query storage cap,
without assuming that any loop body is reached. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady
open SubexponentialSAT BitProgram StructuredCalls SubexpLiftRing SubexpQuarticRing SubexpSetupStorage
open NodeNative LeafHeadSetupProgram MomentsProgram MomentsAssembly
open LeafParametersProgram MulticolorTypes ProducedQueryResources
noncomputable section

 theorem query_reference_input_of_static
    (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ) (hg : Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q))
    (node : Fin (problem query k hg).Q) {a b : NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) a b)
    (ha : Ready (Native.queryInputsAddressed query k hg first tail node) a)
    (input : ℕ) (hb : WordBound input a) {d : ℕ}
    (q : Factor.Spec (problem query k hg).r (problem query k hg).Q (ambient query) d)
    (hf : FactorStatic (s:=Native.queryInputsAddressed query k hg first tail node) q a)
    (hprecision : a.stacks 212=List.replicate q.u true) (hnf : NodeFacts q b.stacks)
    (ht : q.p.t=(produce (query.input k)).t) (hd : d=(produce (query.input k)).d)
    (hu : q.u=(produce (query.input k)).t) (hj : q.J=(produce (query.input k)).J)
    (hR : q.p.R=(produce (query.input k)).R) :
    let A := NodeEnvelope.queryStorageCap query k occurrence qi hg first tail node input
    FactorReady.Input q (FactorResource.sourceCap q A A A) A
      (assignmentBase q (List.replicate d true) (referenceHigh (ambient query) b.stacks)) := by
  dsimp only
  have hs := NodeEnvelope.query_stream_bound query k occurrence qi hg first tail node pr ha input hb
  have hRQ : q.p.R+1 ≤ (produce (query.input k)).Q := by
    rw [hR]
    have h2 := hg.2.2.2.2.2.2.1
    have h4 := hg.2.2.2.2.2.2.2.1
    omega
  have h := preparation_reference_input pr ha input _ hb q hf hnf hprecision hs hRQ
  have heq : NodeEnvelope.assignmentCap (Native.queryInputsAddressed query k hg first tail node)
      input (NodeEnvelope.streamCap (ambient query) input
        ((problem query k hg).Q*(problem query k hg).r)
        (resources query k occurrence qi hg first tail).headSize
        (CostAssembly.assembledWork k (ambient query) (resources query k occurrence qi hg first tail)))
      (baseWidth 3 q.p.t) d q.u q.J =
      NodeEnvelope.queryStorageCap query k occurrence qi hg first tail node input := by
    rw [ht,hu,hj,hd]
    rfl
  dsimp only at h
  rwa [heq] at h

end
end SubexponentialSAT.SqrtLog.LeafProgram.PreparedReady

end OAI.Algorithms
