import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgramStorage

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

def coefficientRegs (regs : Fin 16 → Bool) (a b : Bool) : Fin 16 → Bool :=
  Function.update (Function.update (Function.update (Function.update regs 0 false) 1 true) 8 a) 9 b

theorem cellRegisters_injective : Function.Injective cellRegisters := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [cellRegisters]

theorem cellStacks_injective : Function.Injective cellStacks := by
  intro i j h
  fin_cases i; fin_cases j; rfl

theorem readCoefficient_eval (d : Data) (a b : Bool) (tail : List Bool)
    (hs : d.stacks 0=Cell.frame a b++tail) :
    Eval readCoefficient 6 d
      ⟨coefficientRegs d.regs a b,Function.update d.stacks 0 tail⟩ := by
  have hp : projectState cellRegisters cellStacks d=
      Cell.state (d.regs ∘ cellRegisters) (Cell.frame a b++tail) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i; exact hs
  have ht := Cell.program_trace (d.regs ∘ cellRegisters) a b tail
  rw [←hp] at ht
  have he := eval_call_from_state Cell.program cellRegisters cellStacks d
    cellRegisters_injective cellStacks_injective ht
  have hf : embedState cellRegisters cellStacks d (Cell.state ![false,true,a,b] tail)=
      (⟨coefficientRegs d.regs a b,Function.update d.stacks 0 tail⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ cellRegisters_injective cellStacks_injective
    · intro i; fin_cases i <;> simp [cellRegisters,coefficientRegs,Cell.state]
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,by simpa [cellRegisters] using h.symm⟩
      have h1 : i≠1 := fun h => hi ⟨1,by simpa [cellRegisters] using h.symm⟩
      have h8 : i≠8 := fun h => hi ⟨2,by simpa [cellRegisters] using h.symm⟩
      have h9 : i≠9 := fun h => hi ⟨3,by simpa [cellRegisters] using h.symm⟩
      simp [coefficientRegs,h0,h1,h8,h9]
    · intro i; fin_cases i; simp [cellStacks,Cell.state]
    · intro i hi
      have h0 : i≠0 := fun h => hi ⟨0,by simpa [cellStacks] using h.symm⟩
      simp [h0]
  simpa only [hf] using he

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
