import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativePreparedContexts
import OAI.Algorithms.SubexponentialSAT.SqrtLog.OuterNativeMassWitness

namespace OAI.Algorithms

/-! Concrete native marked and accepted calls at the outer selector boundary.
All remaining inputs are literal source facts and uniform numeric bounds. -/
namespace SubexponentialSAT.SqrtLog.OuterNativeServices
open SubexponentialSAT BitProgram StructuredCalls LeafProgram LeafOuterProgram
noncomputable section

 theorem saved_worker {a : Data} (h : WorkerEmpty a) :
    WorkerEmpty (LeafOuterNative.savedRegisters LeafOuterNative.callerRegisters a) := by
  intro i
  rw [LeafOuterNative.savedRegisters_eq]
  simp only [Function.update_of_ne (show workerStack i ≠ (895 : Fin 896) by
    intro he; have hv:=congrArg Fin.val he; change i.val=895 at hv; have:=i.isLt; omega)]
  exact h i

 theorem bounded_trial_native {n B k qi : ℕ} (F : OuterQuery.Formula n)
    (a : Data) (ha : StartReady a n (formulaRecords F).length B)
    (width L Q : ℕ) (hm : 0 < (formulaRecords F).length)
    (rows : HashSelectProgram.Records) (bits : List Bool)
    (hk : ∀C∈F,C.length ≤ k) (hn : 2 ≤ n)
    (entry : Data) (hw : WorkerEmpty entry)
    (hs : ∀i,LeafOuterNative.MassSource i → (entry.stacks i).length ≤ L)
    (hmod : BinaryArithmetic.toNat (entry.stacks 782)=(formulaRecords F).length)
    (hamb : BinaryArithmetic.toNat (entry.stacks 785)=n)
    (words : ∀mark, OuterQuery.TrialWords
      (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm (bits::rows)) mark) entry)
    (valid : ∀mark, (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm (bits::rows)) mark).Valid)
    (facts : ∀mark, RuntimeFacts
      (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm (bits::rows)) mark)
      k B qi (markedCoefficient k) (markedExponent k))
    (bound : ∀mark, queryLimit k qi (markedCoefficient k) (markedExponent k)
      (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm (bits::rows)) mark) ≤ Q) :
    Nonempty (LeafOuterNative.BoundedMassWitness k entry
      (massScore (formulaClauses F) width rows bits) L Q) := by
  let q := fun ref => OuterQuery.query F a
    (OuterQuery.Count.payloadRows F width hm (bits::rows)) (some (referenceMark hm ref))
  have queries := massQueries_of_contexts k B qi _ (saved_worker hw) q
    (referenceCount F hm width (bits::rows)) (ValidReference hm)
    (fun ref _ => trialWords_saved (words (some (referenceMark hm ref))))
    (fun ref _ => valid _) (fun _ _ => rfl)
    (fun ref hr => reference_query_index F a hm _ ref hr)
    (fun ref _ => by
      rw [OuterQuery.query_ambient F a ha]
      exact hn)
    (fun ref _ => facts _) (by
      intro ref hr base input V J p hV hJ
      exact marked_prepared_context F a ha width hm (bits::rows)
        (some (referenceMark hm ref)) hk base input (facts _) (valid _)
        (by rw [OuterQuery.query_ambient F a ha]; exact hn) p)
  exact bounded_mass_witness k F hm entry width L Q rows bits hw hs hmod hamb
    (fun ref => queryLimit k qi (markedCoefficient k) (markedExponent k) (q ref))
    (fun ref => queryLimit k qi (markedCoefficient k) (markedExponent k) (q ref)+1)
    queries (fun ref _ => bound _)

 theorem final_native {n B k qi : ℕ} (F : OuterQuery.Formula n)
    (a : Data) (ha : StartReady a n (formulaRecords F).length B)
    (width Q : ℕ) (hm : 0 < (formulaRecords F).length)
    (rows : HashSelectProgram.Records) (hk : ∀C∈F,C.length ≤ k) (hn : 2 ≤ n)
    (entry : Data) (hw : WorkerEmpty entry)
    (words : OuterQuery.FinalWords
      (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none) entry)
    (valid : (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none).Valid)
    (facts : RuntimeFacts (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none)
      k B qi (acceptedCoefficient k) (acceptedExponent k))
    (bound : queryLimit k qi (acceptedCoefficient k) (acceptedExponent k)
      (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none) ≤ Q) :
    ∃t out,t ≤ Q ∧ Eval (Query.accepted k) t
      (projectState id workerStack (LeafOuterNative.finalStaged entry)) out ∧
      BinaryArithmetic.toNat (out.stacks 323)=OuterQuery.Count.selectorCount F width rows none ∧
      out.stacks 767=[] := by
  let base := projectState id workerStack (LeafOuterNative.finalStaged entry)
  have input := final_input_from_words entry hw words rfl rfl
  obtain ⟨V,J,p,hV,hJ⟩ := Query.Carried.accepted_construct _ k base valid facts.guard
    input.clean input.sources input.unmarked input.index input.zero input.high
  have hlarge : 2 ≤ ProducedQueryResources.ambient
      (OuterQuery.query F a (OuterQuery.Count.payloadRows F width hm rows) none) := by
    rw [OuterQuery.query_ambient F a ha]; exact hn
  obtain ⟨ctx⟩ := accepted_prepared_context F a ha width hm rows hk base input facts valid hlarge p
  obtain ⟨t,b,ht,he,hvalue,_,hblank⟩ := accepted_of_context base facts input p ctx.execution
    valid hlarge hV hJ ctx.step ctx.stepWidth ctx.referenceBound
  exact ⟨t,b,ht.trans bound,he,hvalue,hblank⟩

end
end SubexponentialSAT.SqrtLog.OuterNativeServices

end OAI.Algorithms
