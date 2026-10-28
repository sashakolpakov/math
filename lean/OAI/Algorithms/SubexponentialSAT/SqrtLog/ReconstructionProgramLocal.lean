import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgramCalls

namespace OAI.Algorithms

/-! Paid cache setup and framing for the lower local Hermite-CRT routine. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Local

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

private def seq (a b : Code) : Code := .seq a b
local infixr:55 " ;; " => seq

abbrev command (localCode : Cmd 16 256) : Code :=
  copy 277 192 ;; copy 243 193 ;; lowerCall localCode 225 244 ;; clearMany [192,193]

def prepared (d : Data) : Data := afterCopy (afterCopy d 277 192 0 1) 243 193 0 1

def budget (zeroBits order K : ℕ) : ℕ := K + 9 * zeroBits + 9 * order + 17

theorem command_run (localCode : Cmd 16 256) (d : Data) (output : List Bool) (K : ℕ)
    (h192 : d.stacks 192 = []) (h193 : d.stacks 193 = []) (h318 : d.stacks 318 = [])
    (hlocal : SubexpConvolutionControl.ExecutesIn localCode K
      ((prepared d).stacks ∘ localPorts)
      (Function.update ((prepared d).stacks ∘ localPorts) 244 output)) :
    ∃ n ≤ budget (d.stacks 277).length (d.stacks 243).length K, ∃ rf,
      Eval (command localCode) n d ⟨rf, Function.update d.stacks 244 output⟩ := by
  have h1 := copy_run d 277 192 (by decide) (by decide) (by decide) h318
  let d1 := afterCopy d 277 192 0 1
  have h2 := copy_run d1 243 193 (by decide) (by decide) (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using h318)
  obtain ⟨nl, hnl, rl, hl⟩ := lowerCall_run localCode 225 244 (prepared d) _ K hlocal
  have he : Function.extend localPorts
      (Function.update ((prepared d).stacks ∘ localPorts) 244 output) (prepared d).stacks =
      Function.update (prepared d).stacks 244 output := by
    rw [ProgramLinking.extend_update localPorts.injective, lower_extend_project]
    rfl
  rw [he] at hl
  let d2 : Data := ⟨rl, Function.update (prepared d).stacks 244 output⟩
  have h3 := clearMany_run d2 [192,193]
  have hfinal : (SubexpSetupStorage.clearManyState [192,193] d2).stacks =
      Function.update d.stacks 244 output := by
    funext i
    by_cases h1 : i = 192 <;> by_cases h2 : i = 193 <;>
      simp [SubexpSetupStorage.clearManyState, SubexpSetupStorage.clearState,
        d2, prepared, afterCopy, StackRoutines.copyStacks, Function.update_apply,
        h1, h2, h192, h193]
  have heq : SubexpSetupStorage.clearManyState [192,193] d2 =
      (⟨(SubexpSetupStorage.clearManyState [192,193] d2).regs,
        Function.update d.stacks 244 output⟩ : Data) := state_ext rfl hfinal
  have hrun := h1.seq (h2.seq (hl.seq h3))
  rw [heq] at hrun
  refine ⟨_, ?_, _, hrun⟩
  simp [budget, d2, d1, prepared, afterCopy, StackRoutines.copyStacks,
    SubexpSetupStorage.clearManyCost, SubexpSetupStorage.clearState, h192, h193]
  omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Local

end OAI.Algorithms
