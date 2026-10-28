import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceRowsProgramInitialize
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram
open SubexponentialSAT BitProgram StructuredCalls

def initializationPorts : Fin 256 → Fin 340 := Fin.castAdd 84
theorem initializationPorts_injective : Function.Injective initializationPorts := Fin.castAdd_injective _ _

def initializeSource : Code := liftCommand LayoutSourceRowsProgramInitialize.command
  210 192 id initializationPorts

def initializeFinish (s : Store) (D W : ℕ) : Store :=
  Function.update (Function.update (Function.update (Function.update s
    243 (List.replicate D true)) 242 (List.replicate (D*W) false))
      192 (List.replicate (D*W) false)) 193 (List.replicate D true)

theorem initializeSource_run (s : Store) (D W : ℕ)
    (h : LayoutSourceRowsProgramInitialize.Ready (s ∘ initializationPorts) D W) :
    ExecutesIn initializeSource (LayoutSourceRowsProgramInitialize.budget D W+1) s
      (initializeFinish s D W) := by
  intro regs
  let a : Data := ⟨regs,s⟩
  obtain ⟨n,rf,hn,he⟩ := LayoutSourceRowsProgramInitialize.command_run
    (s ∘ initializationPorts) D W h regs
  have hc := eval_liftCommand_from_state LayoutSourceRowsProgramInitialize.command
    210 192 id initializationPorts a Function.injective_id initializationPorts_injective he
  let out : State 16 256 := ⟨rf,LayoutSourceRowsProgramInitialize.finish (s ∘ initializationPorts) D W⟩
  have hs : (embedState id initializationPorts a out).stacks=initializeFinish s D W := by
    change Function.extend initializationPorts
      (LayoutSourceRowsProgramInitialize.finish (s ∘ initializationPorts) D W) s=initializeFinish s D W
    unfold LayoutSourceRowsProgramInitialize.finish initializeFinish
    rw [ProgramLinking.extend_update initializationPorts_injective,
      ProgramLinking.extend_update initializationPorts_injective,
      ProgramLinking.extend_update initializationPorts_injective,
      ProgramLinking.extend_update initializationPorts_injective]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project id initializationPorts a Function.injective_id initializationPorts_injective)
    change Function.extend initializationPorts (s ∘ initializationPorts) s=s at hb
    rw [hb]
    rfl
  have hout : embedState id initializationPorts a out=
      (⟨(embedState id initializationPorts a out).regs,initializeFinish s D W⟩ : Data) := by
    apply SubexpScanPrimitives.state_ext
    · rfl
    · exact hs
  change Eval initializeSource (n+1) a (embedState id initializationPorts a out) at hc
  rw [hout] at hc
  exact ⟨n+1,(embedState id initializationPorts a out).regs,by omega,hc⟩

end SubexponentialSAT.SqrtLog.LayoutSourceRowsProgram

end OAI.Algorithms
