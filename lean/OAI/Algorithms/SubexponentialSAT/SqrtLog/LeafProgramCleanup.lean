import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.BankRoutines

namespace OAI.Algorithms

/-! Paid restoration of the isolated count-query worker. The selector's mass
contract requires literal frame preservation, so all 340 worker stacks and all
22 registers are restored by actual instructions after exporting the score. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Cleanup

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

abbrev Data := State 22 340

def reset {r s : ℕ} : List (Fin r) → Cmd r s
  | [] => .base .skip
  | i::is => .seq (.base (.atom (.set i false))) (reset is)

def resetState {r s : ℕ} : List (Fin r) → State r s → State r s
  | [], a => a
  | i::is, a => resetState is ((StructuredProgram.Atom.set i false).eval a)

theorem reset_eval {r s : ℕ} (is : List (Fin r)) (a : State r s) :
    Eval (reset is) is.length a (resetState is a) := by
  induction is generalizing a with
  | nil => exact .base (.skip a)
  | cons i is ih =>
      simpa only [reset,resetState,List.length_cons,Nat.add_comm] using
        (Eval.base (StructuredProgram.Eval.atom (.set i false) a)).seq
          (ih ((StructuredProgram.Atom.set i false).eval a))

theorem reset_stacks {r s : ℕ} (is : List (Fin r)) (a : State r s) :
    (resetState is a).stacks = a.stacks := by
  induction is generalizing a with
  | nil => rfl
  | cons i is ih => exact ih _

theorem reset_regs {r s : ℕ} (is : List (Fin r)) (a : State r s) (i : Fin r) :
    (resetState is a).regs i = if i ∈ is then false else a.regs i := by
  induction is generalizing a with
  | nil => simp [resetState]
  | cons j is ih =>
      rw [resetState,ih]
      by_cases hj : i = j <;> by_cases hi : i ∈ is <;>
        simp [hj,hi,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg,execInstr]

def blank : Data := ⟨fun _ => false,fun _ => []⟩

abbrev command : Cmd 22 340 :=
  .seq (BankRoutines.clearCmd 339 0 1 (List.finRange 340)) (reset (List.finRange 22))

def bytes (a : Data) : ℕ := ((List.finRange 340).map (fun i => (a.stacks i).length)).sum

def budget (a : Data) : ℕ := 2*bytes a + 1045

theorem command_eval (a : Data) (htmp : a.stacks 339 = []) :
    Eval command (budget a) a blank := by
  have hc := BankRoutines.clear_eval (339 : Fin 340) (0 : Fin 22) 1 (List.finRange 340)
    (List.nodup_finRange 340) a.regs a.stacks htmp
  let middle : Data := ⟨readRegs a.regs 0 1 none,
    BankRoutines.clearBankStacks (List.finRange 340) a.stacks⟩
  have hr := reset_eval (List.finRange 22) middle
  have he : resetState (List.finRange 22) middle = blank := by
    cases hs : resetState (List.finRange 22) middle with
    | mk regs stk =>
      have hhregs : regs = fun _ => false := by
        funext i
        have h := reset_regs (List.finRange 22) middle i
        simpa [hs] using h
      have hhstacks : stk = fun _ => [] := by
        have h := reset_stacks (List.finRange 22) middle
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

theorem program_run (a : Data) (htmp : a.stacks 339 = []) :
    RunsIn program (budget a+1) (a.withPC (some program.entry)) (blank.withPC none) :=
  ⟨budget a+1,le_rfl,compiled_halt_trace (command_eval a htmp) 0 0⟩

/-- Arbitrary enclosing memory is preserved by relocation. -/
theorem lifted {r s : ℕ} (register : Fin 22 → Fin r) (stack : Fin 340 → Fin s)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (frame : State r s) (a : Data) (htmp : a.stacks 339 = []) :
    Eval (.call (ProgramLinking.liftProgram program register stack)) (budget a+1)
      (embedState register stack frame a) (embedState register stack frame blank) :=
  eval_call_lifted program register stack frame hr hs
    (compiled_halt_trace (command_eval a htmp) 0 0)

end SubexponentialSAT.SqrtLog.LeafProgram.Cleanup

end OAI.Algorithms
