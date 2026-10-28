import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! Paid conversion from descending high mask to forward high mask. The
descending mask is retained for the high-assignment iterator. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 2 4
abbrev state (regs : Fin 2 → Bool) (source work output tmp : List Bool) : Data :=
  ⟨regs, ![source, work, output, tmp]⟩
abbrev command : Cmd 2 4 :=
  .seq (.call (StackRoutines.copyProgram 0 1 3 0 1))
    (.call (StackRoutines.transferProgram 1 2 0 1))
def program := compiled command 0 2

theorem command_eval (regs : Fin 2 → Bool) (mask : List Bool) :
    ∃ rf, Eval command (10 * mask.length + 8)
      (state regs mask [] [] []) (state rf mask [] mask.reverse []) := by
  let r := readRegs regs 0 1 none
  have hc : Eval (.call (StackRoutines.copyProgram 0 1 3 0 1)) (7 * mask.length + 5)
      (state regs mask [] [] []) (state r mask mask [] []) := by
    have h := ListRegisterProgram.copy_run (0 : Fin 4) 1 3 (0 : Fin 2) 1
      (by decide) (by decide) (by decide) (by decide) regs (state regs mask [] [] []).stacks rfl
    have hs : StackRoutines.copyStacks 0 1 (state regs mask [] [] []).stacks =
        (state r mask mask [] []).stacks := by
      funext i; fin_cases i <;> simp [StackRoutines.copyStacks ]
    apply Eval.call
    simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, r, hs] using h
  have ht : Eval (.call (StackRoutines.transferProgram 1 2 0 1)) (3 * mask.length + 3)
      (state r mask mask [] []) (state (readRegs r 0 1 none) mask [] mask.reverse []) := by
    have h := ListRegisterProgram.transfer_run (1 : Fin 4) 2 (0 : Fin 2) 1
      (by decide) (by decide) r (state r mask mask [] []).stacks
    have hs : StackRoutines.transferStacks 1 2 (state r mask mask [] []).stacks =
        (state (readRegs r 0 1 none) mask [] mask.reverse []).stacks := by
      funext i; fin_cases i <;> simp [StackRoutines.transferStacks ]
    apply Eval.call
    simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC, r, hs] using h
  exact ⟨_, by convert hc.seq ht using 1 ; omega⟩

theorem runsIn (regs : Fin 2 → Bool) (mask : List Bool) :
    ∃ rf, RunsIn program (10 * mask.length + 9)
      ((state regs mask [] [] []).withPC (some program.entry))
      ((state rf mask [] mask.reverse []).withPC none) := by
  obtain ⟨rf, he⟩ := command_eval regs mask
  refine ⟨rf, 10 * mask.length + 8 + 1, by omega, compiled_halt_trace he 0 2⟩

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Mask

end OAI.Algorithms
