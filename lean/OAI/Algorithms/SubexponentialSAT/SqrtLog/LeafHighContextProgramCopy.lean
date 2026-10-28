import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHighContextProgramFlatten

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.BlockSearchPreparation

theorem copy_mask_eval (regs : Fin 4 → Bool) (counter mask forward high : List Bool) :
    Eval copyMask (7*mask.length+5)
      (state regs counter mask forward [] [] [] high [] [] [])
      (state (readRegs regs 0 1 none) counter mask forward [] [] [] high mask [] []) := by
  let a := state regs counter mask forward [] [] [] high [] [] []
  have h := ListRegisterProgram.copy_run (1 : Fin 10) 7 8 (0 : Fin 4) 1
    (by decide) (by decide) (by decide) (by decide) regs a.stacks rfl
  have hs : StackRoutines.copyStacks 1 7 a.stacks =
      (state (readRegs regs 0 1 none) counter mask forward [] [] [] high mask [] []).stacks := by
    funext i; fin_cases i <;> simp [a,state,tapes,StackRoutines.copyStacks]
  have hlen : (a.stacks (1 : Fin 10)).length = mask.length := by rfl
  apply Eval.call
  rw [hlen, hs] at h
  simpa only [a, state, StructuredProgram.State.withPC] using h


end SubexponentialSAT.SqrtLog.LeafHighContextProgram.Local

end OAI.Algorithms
