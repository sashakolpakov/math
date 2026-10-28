import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCommand

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

theorem countHashes_eval (a : Data) (records : List (List Bool))
    (hi : a.stacks 701=Encoding.encodeList id records)
    (ho : a.stacks 704=[]) (h647 : a.stacks 647=[]) (h679 : a.stacks 679=[]) :
    ∃ b, Eval countHashes (SubexpScopeCountSetup.countBudget records) a b ∧
      b.stacks 704=List.replicate records.length true ∧
      (∀ i, i≠704 → b.stacks i=a.stacks i) := by
  have hc := copy_eval a 701 647 ⟨by decide,by decide,by decide,h679⟩
  let c := copied a 701 647
  have hp : projectState r2 countPorts c=SubexpScopeCountSetup.counterState (c.regs 0) (c.regs 1)
      (Encoding.encodeList id records) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> simp [countPorts,c,copied_stack,hi,ho,h647,
ParserProgram.pair]
  have ht := SubexpScopeCountSetup.counter_trace records (c.regs 0) (c.regs 1)
  rw [←hp] at ht
  let small := SubexpScopeCountSetup.counterState false false [] (List.replicate records.length true)
  let b := embedState r2 countPorts c small
  have he := eval_call_from_state SubexpScopeCountSetup.counterProgram r2 countPorts c
    (registers_injective ..) countPorts_injective ht
  refine ⟨b,?_,?_,?_⟩
  · simpa [countHashes,sequence,SubexpScopeCountSetup.countBudget,hi] using
      hc.seq (he.seq (Eval.base (.skip _)))
  · exact embedState_stack r2 countPorts c small countPorts_injective 1
  · intro i h704
    by_cases h647i : i=647
    · subst i
      exact (embedState_stack r2 countPorts c small countPorts_injective 0).trans h647.symm
    · have hf := embedState_stack_frame r2 countPorts c small i (by
        rintro ⟨j,hj⟩; fin_cases j <;> simp [countPorts] at hj <;> simp_all)
      exact hf.trans (by simp [c,copied_stack,h647i])

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
