import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramSourceBank
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def sourcePorts : Fin 320 → Fin 340 := Fin.castAdd 20
theorem sourcePorts_injective : Function.Injective sourcePorts := Fin.castAdd_injective _ _

def packedSource : Code := .call (ProgramLinking.liftProgram
  LayoutProgram.SourceBank.program id sourcePorts)

theorem packedSource_transport (a : Data) (n : ℕ) (rf : Fin 16 → Bool) (bits : List Bool)
    (he : Eval LayoutProgram.SourceBank.command n (projectState id sourcePorts a)
      (⟨rf,Function.update (a.stacks ∘ sourcePorts) 287 bits⟩ : State 16 320)) :
    ∃ e : Data, Eval packedSource (n+1) a e ∧ e.stacks=Function.update a.stacks 287 bits := by
  let out : State 16 320 := ⟨rf,Function.update (a.stacks ∘ sourcePorts) 287 bits⟩
  have hc := eval_liftCommand_from_state LayoutProgram.SourceBank.command 304 287
    id sourcePorts a Function.injective_id sourcePorts_injective he
  refine ⟨embedState id sourcePorts a out,hc,?_⟩
  change Function.extend sourcePorts (Function.update (a.stacks ∘ sourcePorts) 287 bits)
    a.stacks=Function.update a.stacks 287 bits
  rw [ProgramLinking.extend_update sourcePorts_injective]
  have hb := congrArg StructuredProgram.State.stacks
    (embedState_project id sourcePorts a Function.injective_id sourcePorts_injective)
  change Function.extend sourcePorts (a.stacks ∘ sourcePorts) a.stacks=a.stacks at hb
  rw [hb]
  rfl

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
