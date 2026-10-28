import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimeTotal
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeTimePadding
import OAI.Algorithms.SubexponentialSAT.SqrtLog.NodeEnvelopePadding

namespace OAI.Algorithms

noncomputable section
namespace SubexponentialSAT.SqrtLog.NodeTime
open SubexponentialSAT Subexp SubexpLiftRing SubexpSetupStorage MulticolorTypes
open LeafProgram LeafProgram.NodeNative LeafHeadSetupProgram ProducedQueryResources
open LeafParametersProgram FactorResource

/-- A fixed polynomial for the complete measured interior node budget.
The sole source-interface premise is the actual physical FactorReady.Input;
all scalar, dictionary, incidence, parser, support and bucket caps are derived.
The input factor is the incoming masked physical width, including padding. -/
theorem query_fullBudget_polynomial : ∃ C a b c : ℕ, ∀
    (query : LeafQueryFrontend.Query) (k occurrence qi : ℕ)
    (hg : Guard (query.input k))
    (first : Word (problem query k hg).r (problem query k hg).Q)
    (tail : List (Word (problem query k hg).r (problem query k hg).Q))
    (node : Fin (problem query k hg).Q) {start finish : NodeNative.Data}
    (pr : Preparation (Native.queryInputsAddressed query k hg first tail node) start finish)
    (_ha : Ready (Native.queryInputsAddressed query k hg first tail node) start)
    (input : ℕ), WordBound input start →
    query.Valid → 2 ≤ ambient query → SmallInputs query k (ambient query) →
    ∀ {r Q d : ℕ} (q : Factor.Spec r Q (ambient query) d),
    q.p.t=(produce (query.input k)).t → d=(produce (query.input k)).d →
    q.u=(produce (query.input k)).t →
    q.J=(produce (query.input k)).J →
    start.stacks 243=List.replicate q.J true →
    let A := NodeEnvelope.queryStorageCap query k occurrence qi hg first tail node input
    ∀ (base : Fin 768→List Bool), FactorReady.Input q (sourceCap q A A A) A base →
    let p := resources query k occurrence qi hg first tail
    fullBudget pr (baseWidth 3 q.p.t) d q.u q.J
      A A A (canonicalAssignmentCost q A) A ≤
        C*(input+1)^a*(p.bits+1)^b*(CostAssembly.assembledWork k (ambient query) p+1)^c := by
  obtain ⟨C,e,he⟩ := canonical_padding_polynomial
  refine ⟨10^(1+coefficientExponent)*(C+6)^budgetExponent,(8*e+8)*budgetExponent,
    (75*e+70)*budgetExponent,(9*e+8)*budgetExponent,?_⟩
  intro query k occurrence qi hg first tail node start finish pr ha input hb hv hn hs r Q d q ht hdim hu hj h243
  dsimp only
  intro base hf
  let A := NodeEnvelope.queryStorageCap query k occurrence qi hg first tail node input
  let p := resources query k occurrence qi hg first tail
  let W := CostAssembly.assembledWork k (ambient query) p
  have hA := NodeEnvelope.queryStorageCap_padding query k occurrence qi hg first tail node ha input hb hv hn hs
  obtain ⟨hn',hB,hd',hu',hj'⟩ := produced_dimensions_le query k occurrence qi hg first tail hn hs
  have hd : d ≤ p.bits := hdim.trans_le hd'
  have hbase : 0 < p.labelBase := by change 0 < 2*ambient query*matrixHeight query k+1; omega
  have hheads : 1 ≤ p.heads := make_heads_pos query k occurrence _ _ _ _ _ _
  have hbits : 1 ≤ p.bits := make_bits_pos query k occurrence _ _ _ _ _ _
  have horder : q.J=CostAssembly.jetOrder k (ambient query) p :=
    hj.trans (produced_order_eq query k occurrence qi hg first tail hv)
  have hcost := he q A input p.bits k 8 70 8 p base hf hA hn'
    (by simpa only [ht] using hB) hd (by simpa only [hu] using hu')
    (by simpa only [hj] using hj') horder.le hbase hheads hbits
  have hsupport : SupportProgram.count (ambient query) q.J ≤ W := by
    rw [horder]
    exact CostAssembly.supportCount_le_assembledWork k (ambient query) p hbase hheads hbits
  have hall := query_fullBudget_common query k occurrence qi hg first tail node pr ha input p.bits
    (baseWidth 3 q.p.t) d q.u q.J A (canonicalAssignmentCost q A) hb hn'
    (by simpa only [ht] using hB) hd (by simpa only [hu] using hu')
    (by simpa only [hj] using hj') (by rw [hj]; exact produce_J_pos _) h243 hsupport
  have hsum := sum_padding input p.bits W A (canonicalAssignmentCost q A) C e hA hcost
  change commonSize input p.bits W A (canonicalAssignmentCost q A)+1 ≤ _ at hsum
  apply hall.trans
  calc
    _ ≤ 10^(1+coefficientExponent)*
        ((C+6)*combinedPadding input p.bits W e)^budgetExponent :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' hsum budgetExponent)
    _ = _ := by
      unfold combinedPadding
      exact padding_power (10^(1+coefficientExponent)) (C+6) input p.bits W
        (8*e+8) (75*e+70) (9*e+8) budgetExponent

end SubexponentialSAT.SqrtLog.NodeTime

end

end OAI.Algorithms
