import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeKernels
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeQueryTrial

namespace OAI.Algorithms

/-! Accepted-query input and execution join, retaining literal source padding
and deriving output width from the paid native trace. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafParametersProgram ProducedQueryResources

structure AcceptedInputFacts (q : LeafQueryFrontend.Query) (a : Query.Data) : Prop where
  clean : Query.CleanWork a
  sources : Query.Sources q a
  unmarked : q.mark=none
  index : q.index=[false]
  reference : a.stacks 321=[]
  zero : a.stacks 323=[]
  high : ∀i : Fin 768,744 ≤ i.val → a.stacks i=[]

 theorem final_input_from_words {q : LeafQueryFrontend.Query}
    (a : LeafOuterProgram.Data) (ha : LeafOuterProgram.WorkerEmpty a)
    (words : OuterQuery.FinalWords q a) (hm : q.mark=none) (hi : q.index=[false]) :
    AcceptedInputFacts q (projectState id LeafOuterProgram.workerStack (LeafOuterNative.finalStaged a)) := by
  refine ⟨LeafOuterNative.final_clean a ha,LeafOuterNative.final_sources words,hm,hi,?_,?_,?_⟩
  · change (LeafOuterNative.finalStaged a).stacks 321=[]
    rw [LeafOuterNative.finalStaged_frame a 321 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ha 321
  · change (LeafOuterNative.finalStaged a).stacks 323=[]
    rw [LeafOuterNative.finalStaged_frame a 323 (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact ha 323
  · intro i hi
    change (LeafOuterNative.finalStaged a).stacks (LeafOuterProgram.workerStack i)=[]
    rw [LeafOuterNative.finalStaged_frame]
    · exact ha i
    all_goals intro he; have hv := congrArg Fin.val he
              dsimp [LeafOuterProgram.workerStack] at hv; omega

 theorem accepted_of_context
    {q : LeafQueryFrontend.Query} {k B qi count budget width V L : ℕ}
    (a : Query.Data) (facts : RuntimeFacts q k B qi (acceptedCoefficient k) (acceptedExponent k))
    (input : AcceptedInputFacts q a)
    (p : Query.Preparation q k (Query.unmarkedInput (Query.Carried.reference a)) facts.guard
      (Query.Carried.acceptedWidth a) V L)
    (ctx : Marked.Wide.BranchContext Residual.command
      (Marked.Wide.maskCopied (Query.prepared p.out))
      (Query.ProtectedWork (Query.Carried.reference a)) count budget width)
    (hv : q.Valid) (hn : 2 ≤ ambient q)
    (hV : V=Query.modelValueCap (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) p.lengths)))
    (hL : L=Query.modelLengthCap (Circuit.result Serialization.code
      (Execute.guardedModel (q.input k) p.lengths)))
    (hstep : ctx.stepBudget ≤ Query.Cost.residualCap (Query.Cost.ordinaryCap p B qi)
      (Query.Cost.nodeCap p B qi Query.Cost.nodeCoefficient Query.Cost.nodeInputExponent
        Query.Cost.nodeScalarExponent Query.Cost.nodeWorkExponent))
    (hwidth : ctx.stepWidth ≤ Query.Cost.ordinaryCap p B qi)
    (hreference : ctx.referenceBound ≤ Query.Cost.ordinaryCap p B qi) :
    ∃ t b, t ≤ queryLimit k qi (acceptedCoefficient k) (acceptedExponent k) q ∧
      Eval (Query.accepted k) t a b ∧
      BinaryArithmetic.toNat (b.stacks 323)=count ∧
      (b.stacks 323).length ≤ queryLimit k qi (acceptedCoefficient k) (acceptedExponent k) q+1 ∧
      b.stacks 767=[] := by
  obtain ⟨t,b,ht,he,hspace,h320,h322,hvalue,hl,h16,h17,h18,h321,h324⟩ :=
    acceptedKernel k q a facts.guard V L p B qi count budget width ctx hv
      input.clean input.sources input.unmarked input.index input.zero input.high hn facts.small
      hV hL hstep hwidth hreference
  have hcost := facts.source_cost_le a input.sources
    (by rw [input.reference]; simp) facts.guard p.firstWord p.remainingWords
      p.alphabetNodup p.alphabetComplete
  have ht' := ht.trans hcost
  have hlen := LeafOuterNative.eval_stack_length he 323
  rw [input.zero,List.length_nil] at hlen
  refine ⟨t,b,ht',he,hvalue,by omega,?_⟩
  exact (workspace_eq_at hspace 767 (Or.inr (by decide))).trans (input.high 767 (by decide))

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
