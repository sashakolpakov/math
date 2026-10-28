import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramArithmetic
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramPad

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ModularPrograms

theorem paddingStacks_injective : Function.Injective paddingStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [paddingStacks]

def paddedStacks (d : Data) : Fin 64 → List Bool :=
  Function.update
    (Function.update (Function.update d.stacks 25 []) 23
      ((d.stacks 23).drop (d.stacks 25).length)) 13
    ((SubexpLiftRing.fixedBits (d.stacks 25).length (BinaryArithmetic.toNat (d.stacks 23))).reverse++d.stacks 13)

theorem padding_call_eval (d : Data)
    (h : BinaryArithmetic.toNat (d.stacks 23) < 2^(d.stacks 25).length) :
    ∃ rf, Eval (.call (ProgramLinking.liftProgram paddingProgram low8 paddingStacks))
      (4*(d.stacks 25).length+3) d ⟨rf,paddedStacks d⟩ ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  obtain ⟨rr,ht⟩ := appendWord_trace (d.regs ∘ low8) (d.stacks 25)
    (d.stacks 23) (d.stacks 13) h
  let a : State 8 3 := ⟨d.regs ∘ low8,operandStacks (d.stacks 25) (d.stacks 23) (d.stacks 13)⟩
  let b : State 8 3 := ⟨rr,operandStacks [] ((d.stacks 23).drop (d.stacks 25).length)
    ((SubexpLiftRing.fixedBits (d.stacks 25).length (BinaryArithmetic.toNat (d.stacks 23))).reverse++d.stacks 13)⟩
  have hin : embedState low8 paddingStacks d a=d := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective paddingStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i; fin_cases i <;> simp [a,paddingStacks,operandStacks]
    · intro i hi; rfl
  let rf := Function.extend low8 rr d.regs
  have hout : embedState low8 paddingStacks d b=⟨rf,paddedStacks d⟩ := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective paddingStacks_injective
    · intro i; exact low8_injective.extend_apply rr d.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [paddedStacks,b,paddingStacks,operandStacks]
    · intro i hi
      have h25 : i≠25 := fun h => hi ⟨0,by simpa [paddingStacks] using h.symm⟩
      have h23 : i≠23 := fun h => hi ⟨1,by simpa [paddingStacks] using h.symm⟩
      have h13 : i≠13 := fun h => hi ⟨2,by simpa [paddingStacks] using h.symm⟩
      simp [paddedStacks,h25,h23,h13]
  have ht' : Trace paddingProgram (4*(d.stacks 25).length+3)
      (a.withPC (some paddingProgram.entry)) (b.withPC none) := by
    simpa [a,b,paddingCfg,StructuredProgram.State.withPC] using ht
  have he := eval_call_lifted paddingProgram low8 paddingStacks d
    low8_injective paddingStacks_injective ht'
  refine ⟨rf,by simpa only [hin,hout] using he,?_⟩
  intro i hi
  apply Function.extend_apply'
  rintro ⟨j,hj⟩
  have hh := congrArg Fin.val hj
  have hjlt := j.isLt
  dsimp [low8] at hh
  omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
