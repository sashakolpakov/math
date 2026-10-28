import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeReferences
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterNativePolynomial

namespace OAI.Algorithms

/-! Every collector callback inherits the exact staged trial sources while
its queue and accumulator remain arbitrary. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram

structure MarkedInputFacts (q : LeafQueryFrontend.Query) (a : Query.Data) : Prop where
  clean : Query.CleanWork a
  sources : Query.Sources q a
  marked : q.mark.isSome=true
  reference : a.stacks 321=q.index.reverse
  zero : a.stacks 323=[]
  high : ∀i : Fin 768,744 ≤ i.val → a.stacks i=[]

 theorem trialWords_saved {q : LeafQueryFrontend.Query} {a : Data}
    (h : OuterQuery.TrialWords q a) :
    OuterQuery.TrialWords q (LeafOuterNative.savedRegisters LeafOuterNative.callerRegisters a) := by
  constructor
  · constructor
    · simpa [LeafOuterNative.savedRegisters_eq] using h.formula
    · simpa [LeafOuterNative.savedRegisters_eq] using h.modulus
    · simpa [LeafOuterNative.savedRegisters_eq] using h.width
    · simpa [LeafOuterNative.savedRegisters_eq] using h.ambient
  · simpa [LeafOuterNative.savedRegisters_eq] using h.rows

 theorem reference_load_workspace (a b : Data) (stream : List Bool)
    (hb : b.stacks=Function.update (LeafOuterNative.trialStaged a).stacks 320 stream) :
    Marked.Wide.workspace (projectState id workerStack b)=
      Marked.Wide.workspace (projectState id workerStack (LeafOuterNative.trialStaged a)) := by
  funext j
  have hj : workerStack (Marked.Wide.workPort j)≠320 := by
    intro he
    have he' : Marked.Wide.workPort j=320 := Fin.castAdd_injective 768 128 he
    have hv := congrArg Fin.val he'
    dsimp [Marked.Wide.workPort] at hv
    split_ifs at hv <;> simp only at hv <;> omega
  change b.stacks (workerStack (Marked.Wide.workPort j))=_
  rw [hb,Function.update_of_ne hj]
  rfl

 theorem marked_input_from_trial {q : LeafQueryFrontend.Query}
    (a : Data) (ha : WorkerEmpty a) (words : OuterQuery.TrialWords q a)
    (hm : q.mark.isSome=true) (bits : List Bool) (href : q.index=bits)
    (b : Data) (stream : List Bool)
    (hb : b.stacks=Function.update (LeafOuterNative.trialStaged a).stacks 320 stream)
    (base : Query.Data) (tail : List Bool)
    (hbase : Marked.Wide.invariant
      (fun w => w=Marked.Wide.workspace (projectState id workerStack b)) base) :
    MarkedInputFacts q (markedStart base tail bits) := by
  let source := projectState id workerStack (LeafOuterNative.trialStaged a)
  have hwork : Marked.Wide.workspace base=Marked.Wide.workspace source :=
    hbase.1.trans (reference_load_workspace a b stream hb)
  refine ⟨marked_start_clean source base tail bits (LeafOuterNative.trial_clean a ha)
    hwork hbase.2.2,
    marked_start_sources q source base tail bits (LeafOuterNative.trial_sources words) hwork,
    hm,?_,marked_start_zero base tail bits hbase.2.1,
    marked_start_high source base tail bits (trial_high_empty a ha) hwork⟩
  rw [marked_start_reference,href]

end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
