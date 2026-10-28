import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.ExecutionController
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-! Fixed local commands embedded as main-controller procedures. Port maps
are static program data; local transitions and the return instruction are
charged explicitly. No input or output word is installed by executable fiat. -/

namespace SubexponentialSAT.SqrtLog.Execution

open BitProgram StructuredCalls SubexpMainProgram

abbrev procedureOfCommand {er es r s : ℕ} (command : Cmd r s)
    (input output : Fin s) (register : Fin r ↪ Fin (workRegs er))
    (stack : Fin s ↪ Fin (totalStacks es)) : Procedure er es where
  registers := r
  stackCount := s
  labels := size command + 1
  program := compiled command input output
  register := register
  stack := stack

theorem procedureOfCommand_eval {er es r s : ℕ} (command : Cmd r s)
    (input output : Fin s) (register : Fin r ↪ Fin (workRegs er))
    (stack : Fin s ↪ Fin (totalStacks es)) (a : MainState er es)
    {steps : ℕ} {result : StructuredProgram.State r s}
    (execution : Eval command steps
      ((procedureOfCommand command input output register stack).project a) result) :
    Eval (procedureOfCommand command input output register stack).invoke (steps + 1)
      a ((procedureOfCommand command input output register stack).install a result) := by
  apply Procedure.invoke_trace
  exact compiled_halt_trace execution input output

/-- A framed local I/O contract is sufficient for invoking the same fixed
program in any main state with those projected local values. -/
theorem procedureOfCommand_io {er es r s : ℕ} (command : Cmd r s)
    (input output : Fin s) (register : Fin r ↪ Fin (workRegs er))
    (stack : Fin s ↪ Fin (totalStacks es)) (a : MainState er es)
    (xs ys : List Bool) {steps : ℕ}
    (ready : (procedureOfCommand command input output register stack).project a =
      StructuredProgram.ioState input xs)
    (execution : Eval command steps (StructuredProgram.ioState input xs)
      (StructuredProgram.ioState output ys)) :
    Eval (procedureOfCommand command input output register stack).invoke (steps + 1)
      a ((procedureOfCommand command input output register stack).install a
        (StructuredProgram.ioState output ys)) := by
  apply procedureOfCommand_eval
  simpa only [ready] using execution

theorem procedure_install_stack_frame {er es : ℕ} (p : Procedure er es)
    (a : MainState er es) (result : StructuredProgram.State p.registers p.stackCount)
    (j : Fin (totalStacks es)) (outside : ¬ ∃ i, p.stack i = j) :
    (p.install a result).stacks j = a.stacks j := by
  exact embedState_stack_frame p.registerMap p.stack a result j outside

end SubexponentialSAT.SqrtLog.Execution

end OAI.Algorithms
