import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeQuerySize
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativePolynomial

namespace OAI.Algorithms

/-! Assemble the exact native marked-query contract from the actual prepared
branch context. All resource and source premises are discharged here; the
remaining context is the concrete residual/count service. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafParametersProgram ProducedQueryResources

 theorem polynomialMarked_of_context
    {q : LeafQueryFrontend.Query} {k B qi CK x y z C e count budget width V L : ℕ}
    (a : Query.Data) (facts : RuntimeFacts q k B qi C e)
    (p : Query.Preparation q k (Query.markedInput (Query.Carried.reference a)) facts.guard
      (Query.Carried.markedWidth a) V L)
    (ctx : Marked.Wide.BranchContext Residual.command
      (Marked.Wide.maskCopied (Query.prepared p.out))
      (Query.ProtectedWork (Query.Carried.reference a)) count budget width)
    (hv : q.Valid) (hc : Query.CleanWork a) (hs : Query.Sources q a)
    (hm : q.mark.isSome=true) (href : a.stacks 321=q.index.reverse)
    (hzero : a.stacks 323=[]) (hhigh : ∀i : Fin 768,744 ≤ i.val → a.stacks i=[])
    (hn : 2 ≤ ambient q)
    (hV : V=Query.modelValueCap (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) p.lengths)))
    (hL : L=Query.modelLengthCap (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) p.lengths)))
    (hstep : ctx.stepBudget ≤ Query.Cost.residualCap (Query.Cost.ordinaryCap p B qi)
      (Query.Cost.nodeCap p B qi CK x y z))
    (hwidth : ctx.stepWidth ≤ Query.Cost.ordinaryCap p B qi)
    (hreference : ctx.referenceBound ≤ Query.Cost.ordinaryCap p B qi) :
    Nonempty (LeafOuterNative.PolynomialMarked k CK x y z C e a count
      (queryLimit k qi C e q) width) := by
  exact ⟨{
    query := q, guard := facts.guard, V := V, L := L, preparation := p,
    occurrence := B, qi := qi, branchBudget := budget, context := ctx,
    queryValid := hv, clean := hc, sources := hs, marked := hm,
    reference := href, zero := hzero, highEmpty := hhigh, ambientLarge := hn,
    small := facts.small, valueCap := hV, lengthCap := hL, step := hstep,
    stepWidth := hwidth, referenceBound := hreference,
    cost := facts.source_cost a hs href facts.guard p.firstWord p.remainingWords
      p.alphabetNodup p.alphabetComplete }⟩

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
