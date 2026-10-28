import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramPreparedReadyReferenceQuery
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopeQueryCaps

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT SubexpLiftRing SubexpSetupStorage MulticolorTypes
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram ProducedQueryResources
open LeafParametersProgram FactorResource PreparedReady

/-- The complete node bound from actual prepared source and cache identities.
A synthetic bounded reference discharges the source-cost interface even when
no assignment is visited. The dense size arguments are all the same A. -/
theorem prepared_fullBudget_polynomial : ∃ C a b c : ℕ, ∀
    (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
    (hg : Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q))
    (node : Fin (problem query k hg).Q) {start finish : NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) start finish)
    (_ha : Ready (Native.queryInputsAddressed query k hg first tail node) start)
    (input : ℕ), WordBound input start →
    query.Valid → 2 ≤ ambient query → SmallInputs query k (ambient query) →
    ∀ {d : ℕ} (q : Factor.Spec (problem query k hg).r (problem query k hg).Q (ambient query) d),
    FactorStatic (s:=Native.queryInputsAddressed query k hg first tail node) q start →
    NodeFacts q finish.stacks → start.stacks 212=List.replicate q.u true →
    q.p.t=(produce (query.input k)).t → d=(produce (query.input k)).d →
    q.u=(produce (query.input k)).t → q.J=(produce (query.input k)).J →
    q.p.R=(produce (query.input k)).R →
    let A := NodeEnvelope.queryStorageCap query k occurrence qi hg first tail node input
    let p := resources query k occurrence qi hg first tail
    fullBudget pr (baseWidth 3 q.p.t) d q.u q.J A A A (canonicalAssignmentCost q A) A ≤
      C*(input+1)^a*(p.bits+1)^b*(CostAssembly.assembledWork k (ambient query) p+1)^c := by
  obtain ⟨C,a,b,c,h⟩ := query_fullBudget_polynomial
  refine ⟨C,a,b,c,?_⟩
  intro query k occurrence qi hg first tail node start finish pr ha input hb hv hn hs
    d q hf hnf hprecision ht hd hu hj hR
  have href := query_reference_input_of_static query k occurrence qi hg first tail node
    pr ha input hb q hf hprecision hnf ht hd hu hj hR
  exact h query k occurrence qi hg first tail node pr ha input hb hv hn hs q ht hd hu hj
    hf.target _ href

end SubexponentialSAT.SqrtLog.NodeTime

end

end OAI.Algorithms
