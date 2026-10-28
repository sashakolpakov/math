import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram
import OAI.Algorithms.SubexponentialSAT.ProgramProjection
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-! Concrete sequential composition of top-level procedures. Both finite
tables are installed on the common work-register bank; protected iterator
registers never become available to their code. -/

namespace SubexponentialSAT.SubexpProcedureCompose

open BitProgram StructuredCalls SubexpMainProgram

variable {er es : ℕ}

abbrev localCall (p : Procedure er es) : Cmd (workRegs er) (totalStacks es) :=
  .call (ProgramLinking.liftProgram p.program p.register p.stack)

def workProject (a : MainState er es) : State (workRegs er) (totalStacks es) :=
  projectState (workRegister er) id a

def sequence (first second : Procedure er es) : Procedure er es where
  registers := workRegs er
  stackCount := totalStacks es
  labels := size (.seq (localCall first) (localCall second)) + 1
  program := compiled (.seq (localCall first) (localCall second))
    (first.stack first.program.inputStack) (second.stack second.program.outputStack)
  register := Function.Embedding.refl _
  stack := Function.Embedding.refl _

@[simp] theorem sequence_labels (first second : Procedure er es) :
    (sequence first second).labels = first.labels + second.labels + 1 := rfl

theorem invoke_as_outer (p : Procedure er es) :
    p.invoke = .call (ProgramLinking.liftProgram
      (ProgramLinking.liftProgram p.program p.register p.stack) (workRegister er) id) := by
  rw [ProgramProjection.liftProgram_comp]
  rfl

theorem invoke_project (p : Procedure er es) {n : ℕ} {a b : MainState er es}
    (h : Eval p.invoke n a b) :
    Eval (localCall p) n (workProject a) (workProject b) := by
  rw [invoke_as_outer] at h
  exact ProgramProjection.project_call _ (workRegister er) id
    (workRegister_injective er) Function.injective_id h

theorem invoke_work_frame (p : Procedure er es) {n : ℕ} {a b : MainState er es}
    (h : Eval p.invoke n a b) :
    b = embedState (workRegister er) id a (workProject b) := by
  rw [invoke_as_outer] at h
  exact ProgramProjection.call_frame _ (workRegister er) id
    (workRegister_injective er) Function.injective_id h

theorem embedState_twice {r s R S : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack)
    (frame : State R S) (first second : State r s) :
    embedState register stack (embedState register stack frame first) second =
      embedState register stack frame second := by
  apply embedState_eq_of_ports register stack _ _ second hr hs
  · intro i
    exact embedState_register register stack frame second hr i
  · intro i hi
    rw [embedState_register_frame register stack frame second i hi,
      embedState_register_frame register stack frame first i hi]
  · intro i
    exact embedState_stack register stack frame second hs i
  · intro i hi
    rw [embedState_stack_frame register stack frame second i hi,
      embedState_stack_frame register stack frame first i hi]

/-- Composition starts the second procedure in the first one's actual final
state. The one extra instruction is the compiled sequence's final halt. -/
theorem sequence_invoke (first second : Procedure er es)
    {n m : ℕ} {a b c : MainState er es}
    (hfirst : Eval first.invoke n a b) (hsecond : Eval second.invoke m b c) :
    Eval (sequence first second).invoke (n + m + 1) a c := by
  have hlocal := (invoke_project first hfirst).seq (invoke_project second hsecond)
  have ht := compiled_halt_trace hlocal
    (first.stack first.program.inputStack) (second.stack second.program.outputStack)
  have hs : BitProgram.Trace (sequence first second).program (n + m + 1)
      (((sequence first second).project a).withPC (some (sequence first second).program.entry))
      ((workProject c).withPC none) := ht
  have hrun := Procedure.invoke_trace (sequence first second) a (workProject c) hs
  have hb := invoke_work_frame first hfirst
  have hc := invoke_work_frame second hsecond
  rw [hb, embedState_twice _ _ (workRegister_injective er) Function.injective_id] at hc
  have hend : (sequence first second).install a (workProject c) = c := hc.symm
  simpa only [hend] using hrun

/-- Canonicalize every work register before a phase whose finite trace
contract restores a fixed register frame. Persistent stack data is untouched. -/
def resetWorkRegisters (er es : ℕ) : Procedure er es where
  registers := workRegs er
  stackCount := totalStacks es
  labels := size (@RegisterResetProgram.all (workRegs er) (totalStacks es)) + 1
  program := RegisterResetProgram.program (persistent es 0)
  register := Function.Embedding.refl _
  stack := Function.Embedding.refl _

noncomputable def resetResult (a : MainState er es) : MainState er es :=
  (resetWorkRegisters er es).install a
    (RegisterResetProgram.zeroed ((resetWorkRegisters er es).project a))

theorem reset_invoke (a : MainState er es) :
    Eval (resetWorkRegisters er es).invoke (workRegs er + 1) a (resetResult a) :=
  Procedure.invoke_trace _ a _ (RegisterResetProgram.program_trace (persistent es 0) _)

theorem reset_stacks (a : MainState er es) : (resetResult a).stacks = a.stacks := by
  funext i
  exact embedState_stack (resetWorkRegisters er es).registerMap
    (resetWorkRegisters er es).stack a _ (resetWorkRegisters er es).stack.injective i

theorem reset_work_register (a : MainState er es) (i : Fin (workRegs er)) :
    (resetResult a).regs (workRegister er i) = false :=
  embedState_register (resetWorkRegisters er es).registerMap
    (resetWorkRegisters er es).stack a _ (resetWorkRegisters er es).registerMap_injective i

theorem reset_control_register (a : MainState er es) (i : Fin 3) :
    (resetResult a).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control (resetWorkRegisters er es) a _ i

end SubexponentialSAT.SubexpProcedureCompose

end OAI.Algorithms
