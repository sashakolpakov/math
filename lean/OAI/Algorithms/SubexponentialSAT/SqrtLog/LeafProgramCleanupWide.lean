import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramCleanup

namespace OAI.Algorithms

/-! Full cleanup for the wider leaf worker including setup pockets. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 40 768
def blank : Data := ⟨fun _ => false,fun _ => []⟩
abbrev command : Cmd 40 768 :=
  .seq (BankRoutines.clearCmd 767 0 1 (List.finRange 768)) (reset (List.finRange 40))
def bytes (a : Data) : ℕ := ((List.finRange 768).map (fun i => (a.stacks i).length)).sum
def budget (a : Data) : ℕ := 2*bytes a+2347

theorem command_eval (a : Data) (htmp : a.stacks 767 = []) :
    Eval command (budget a) a blank := by
  have hc := BankRoutines.clear_eval (767 : Fin 768) (0 : Fin 40) 1 (List.finRange 768)
    (List.nodup_finRange 768) a.regs a.stacks htmp
  let middle : Data := ⟨readRegs a.regs 0 1 none,
    BankRoutines.clearBankStacks (List.finRange 768) a.stacks⟩
  have hr := reset_eval (List.finRange 40) middle
  have he : resetState (List.finRange 40) middle = blank := by
    cases hs : resetState (List.finRange 40) middle with
    | mk regs stk =>
      have hhregs : regs = fun _ => false := by
        funext i
        have h := reset_regs (List.finRange 40) middle i
        simpa [hs] using h
      have hhstacks : stk = fun _ => [] := by
        have h := reset_stacks (List.finRange 40) middle
        rw [hs] at h
        change stk = _ at h
        rw [h]
        funext i
        simp [middle,BankRoutines.clearBankStacks]
      simp only [hhregs,hhstacks]
      rfl
  rw [he] at hr
  simpa only [command,budget,bytes,List.length_finRange] using hc.seq hr

def program := compiled command 0 0

theorem program_run (a : Data) (htmp : a.stacks 767 = []) :
    RunsIn program (budget a+1) (a.withPC (some program.entry)) (blank.withPC none) :=
  ⟨budget a+1,le_rfl,compiled_halt_trace (command_eval a htmp) 0 0⟩

theorem lifted {r s : ℕ} (register : Fin 40 → Fin r) (stack : Fin 768 → Fin s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (frame : State r s) (a : Data) (htmp : a.stacks 767 = []) :
    Eval (.call (ProgramLinking.liftProgram program register stack)) (budget a+1)
      (embedState register stack frame a) (embedState register stack frame blank) :=
  eval_call_lifted program register stack frame hr hs
    (compiled_halt_trace (command_eval a htmp) 0 0)

end SubexponentialSAT.SqrtLog.LeafProgram.Cleanup.Wide

end OAI.Algorithms
