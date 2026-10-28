import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramStorage

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem low3_injective : Function.Injective low3 := Fin.castAdd_injective _ _
theorem frameStacks_injective : Function.Injective frameStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [frameStacks]

theorem writeRow_eval (d : Data) :
    ∃ rf, Eval writeRow (4*(d.stacks 13).length+8) d
      ⟨rf,Function.update (Function.update d.stacks 13 []) 12
        (true::(Encoding.frame (d.stacks 13).reverse++d.stacks 12))⟩ ∧
      (∀ i : Fin 16, 3 ≤ i.val → rf i=d.regs i) := by
  let a : State 3 2 := ⟨d.regs ∘ low3,![d.stacks 13,d.stacks 12]⟩
  let b := RowSelectionProgramSelect.frameState false false []
    (Encoding.frame (d.stacks 13).reverse++d.stacks 12)
  let rr := Function.extend low3 b.regs d.regs
  let mid : Data := ⟨rr,Function.update (Function.update d.stacks 13 []) 12
    (Encoding.frame (d.stacks 13).reverse++d.stacks 12)⟩
  have hin : embedState low3 frameStacks d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ low3_injective frameStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> rfl
    · intro i hi; rfl
  have hout : embedState low3 frameStacks d b=mid := by
    apply embedState_eq_of_ports _ _ _ _ _ low3_injective frameStacks_injective
    · intro i; exact low3_injective.extend_apply b.regs d.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [mid,b,frameStacks]
    · intro i hi
      have h13 : i≠13 := fun h => hi ⟨0,by simpa [frameStacks] using h.symm⟩
      have h12 : i≠12 := fun h => hi ⟨1,by simpa [frameStacks] using h.symm⟩
      simp [mid,h13,h12]
  have he := eval_call_lifted RowSelectionProgramSelect.frameProgram low3 frameStacks d
    low3_injective frameStacks_injective
    (RowSelectionProgramSelect.frameProgram_trace (d.regs ∘ low3) (d.stacks 13) (d.stacks 12))
  change Eval (.call (ProgramLinking.liftProgram RowSelectionProgramSelect.frameProgram low3 frameStacks))
    (4*(d.stacks 13).length+6) (embedState low3 frameStacks d a) (embedState low3 frameStacks d b) at he
  rw [hin,hout] at he
  have hp := push_eval 12 true mid
  refine ⟨(pushed 12 true mid).regs,?_,?_⟩
  · convert he.seq hp using 1 ; simp [pushed, mid]
  · intro i hi
    rw [pushed_register 12 true mid i (by omega)]
    change Function.extend low3 b.regs d.regs i=d.regs i
    apply Function.extend_apply'
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have hjlt := j.isLt
    dsimp [low3] at hv
    omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
