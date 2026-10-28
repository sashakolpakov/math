import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramStorage
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramArithmetic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularPrograms SubexponentialSAT.ModularArithmetic

private theorem padTo_empty (xs : List Bool) : padTo xs []=List.replicate xs.length false := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [padTo,List.replicate_succ] using congrArg (List.cons false) ih

private theorem zeroVertexStacks_injective : Function.Injective zeroVertexStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [zeroVertexStacks]

theorem zeroVertex_eval (d : Data) (h2 : d.stacks 2=[]) (h26 : d.stacks 26=[]) :
    ∃ rf, Eval (.call (ProgramLinking.liftProgram paddingProgram low8 zeroVertexStacks))
      (4*(d.stacks 25).length+3) d
      ⟨rf,Function.update (Function.update d.stacks 25 []) 2
        (List.replicate (d.stacks 25).length false)⟩ := by
  obtain ⟨rr,ht⟩ := SubexponentialSAT.SubexpDenseLiteralPadding.padding_trace_any (d.regs ∘ low8)
    (d.stacks 25) [] []
  let a : State 8 3 := ⟨d.regs ∘ low8,operandStacks (d.stacks 25) [] []⟩
  let b : State 8 3 := ⟨rr,operandStacks [] [] (List.replicate (d.stacks 25).length false)⟩
  let rf := Function.extend low8 rr d.regs
  have hin : embedState low8 zeroVertexStacks d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective zeroVertexStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> simp [a,zeroVertexStacks,operandStacks,h2,h26]
    · intro i hi; rfl
  have hout : embedState low8 zeroVertexStacks d b=
      (⟨rf,Function.update (Function.update d.stacks 25 []) 2
        (List.replicate (d.stacks 25).length false)⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective zeroVertexStacks_injective
    · intro i; exact low8_injective.extend_apply rr d.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [b,zeroVertexStacks,operandStacks,h26]
    · intro i hi
      have h25 : i≠25 := fun h => hi ⟨0,by simpa [zeroVertexStacks] using h.symm⟩
      have h2i : i≠2 := fun h => hi ⟨2,by simpa [zeroVertexStacks] using h.symm⟩
      simp [h25,h2i]
  have ht' : Trace paddingProgram (4*(d.stacks 25).length+3)
      (a.withPC (some paddingProgram.entry)) (b.withPC none) := by
    simpa [a,b,paddingCfg,StructuredProgram.State.withPC,padTo_empty] using ht
  have he := eval_call_lifted paddingProgram low8 zeroVertexStacks d
    low8_injective zeroVertexStacks_injective ht'
  exact ⟨rf,by simpa only [hin,hout] using he⟩

def initialStacks (d : Data) : Fin 64 → List Bool :=
  Function.update (Function.update d.stacks 12 [false]) 2 (List.replicate (d.stacks 11).length false)

theorem initialize_eval (d : Data) (h2 : d.stacks 2=[]) (h12 : d.stacks 12=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[]) (h26 : d.stacks 26=[]) :
    ∃ rf, Eval initializeCommand (11*(d.stacks 11).length+10) d ⟨rf,initialStacks d⟩ := by
  have hp := push_eval 12 false d
  let d0 := pushed 12 false d
  have hc := copy_eval 11 25 d0 (by decide) (by decide) (by decide)
    (by simpa [d0,pushed] using h24)
  let d1 := copied 11 25 d0
  obtain ⟨rf,he⟩ := zeroVertex_eval d1
    (by simpa [d1,d0,copied,StackRoutines.copyStacks,pushed] using h2)
    (by simpa [d1,d0,copied,StackRoutines.copyStacks,pushed] using h26)
  refine ⟨rf,?_⟩
  convert hp.seq (hc.seq he) using 1
  · simp [d1,d0,copied,StackRoutines.copyStacks,pushed,h25] ; omega
  · apply congrArg (StructuredProgram.State.mk rf)
    funext i
    by_cases h25i : i=25
    · subst i; simp [d1,d0,copied,StackRoutines.copyStacks,pushed,initialStacks,h25]
    · by_cases h2i : i=2
      · subst i
        simp [d1,d0,copied,StackRoutines.copyStacks,pushed,initialStacks,h25,h12]
      · simp [d1,d0,copied,StackRoutines.copyStacks,pushed,initialStacks,h25,h12,h25i,h2i]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
