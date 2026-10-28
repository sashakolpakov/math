import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.ListRegisterProgram

namespace OAI.Algorithms

/-! The source-row dimension copy on243 becomes template scratch after
its value has been copied to126. This actual clear establishes that handoff. -/

namespace SubexponentialSAT.SubexpMainNodeScratch

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary)

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 2
  stackCount := 1
  labels := 3
  program := StackRoutines.clearProgram 0 0 1
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨fun _ => ordinary alloc 243, by intro i j _; exact Subsingleton.elim i j⟩

def localResult (a : StructuredProgram.State 2 1) : StructuredProgram.State 2 1 :=
  ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks 0 a.stacks⟩

noncomputable def result {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    MainState er es := (procedure er alloc).install a (localResult ((procedure er alloc).project a))

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  2 * (a.stacks (ordinary alloc 243)).length + 3

theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    Eval (procedure er alloc).invoke (runtimeBound alloc a) a (result alloc a) :=
  Procedure.invoke_trace _ _ _
    (ListRegisterProgram.clear_run (0 : Fin 1) (0 : Fin 2) 1
      ((procedure er alloc).project a).regs ((procedure er alloc).project a).stacks)

theorem result_cleared {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (result alloc a).stacks (ordinary alloc 243) = [] := by
  have h := embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
    (localResult ((procedure er alloc).project a)) (procedure er alloc).stack.injective (0 : Fin 1)
  change (result alloc a).stacks (ordinary alloc 243) =
    (localResult ((procedure er alloc).project a)).stacks 0 at h
  simpa [localResult, StackRoutines.clearStacks] using h

theorem result_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hi : i ≠ ordinary alloc 243) :
    (result alloc a).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  exact hi hj.symm

theorem result_control {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 3) : (result alloc a).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control _ _ _ i

end SubexponentialSAT.SubexpMainNodeScratch

end OAI.Algorithms
