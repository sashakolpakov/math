import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainSparsify
import OAI.Algorithms.SubexponentialSAT.SubexpProcedureCompose

namespace OAI.Algorithms

/-! Canonical register initialization before the actual sparsification
worklist. This closes the caller boundary where normalization may leave
arbitrary work-register values. The splitter must restore the resulting
canonical non-core register frame at each return. -/

namespace SubexponentialSAT.SubexpCanonicalSparsify

open BitProgram StructuredCalls SubexpMainProgram SubexpProcedureCompose

variable {er es labels : ℕ}

abbrev procedure (splitter : Program (workRegs er) (totalStacks es) labels) : Procedure er es :=
  sequence (resetWorkRegisters er es) (SubexpMainSparsify.procedure splitter)

noncomputable abbrev result (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (body leaves : List Bool) : MainState er es :=
  (SubexpMainSparsify.procedure splitter).install (resetResult caller)
    (SubexpMainSparsify.data (SubexpMainSparsify.mainPorts er es)
      ((SubexpMainSparsify.procedure splitter).project (resetResult caller))
      (fun _ => false) [] [] body leaves)

theorem register_frame_zero (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (i : Fin (workRegs er)) :
    ((SubexpMainSparsify.procedure splitter).project (resetResult caller)).regs i = false :=
  reset_work_register caller i

theorem invoke {α : Type*}
    (splitter : Program (workRegs er) (totalStacks es) labels) (caller : MainState er es)
    (ready : SubexpMainSparsify.Ready (SubexpMainSparsify.mainPorts er es)
      ((SubexpMainSparsify.procedure splitter).project caller))
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (P : α → Prop) (cost : α → ℕ) (bound : ℕ) (x : α) (hx : P x)
    (hbody : caller.stacks (persistent es 0) = enc x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.RealizesOn splitter
      (SubexpMainSparsify.mainPorts er es).register (SubexpMainSparsify.mainPorts er es).coreStack
      (SubexpMainSparsify.workFrame (SubexpMainSparsify.mainPorts er es)
        ((SubexpMainSparsify.procedure splitter).project (resetResult caller)) (enc x))
      enc branch.split P cost)
    (hbound : ∀ y, P y → cost y + ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound) :
    ∃ steps, steps ≤ SubexpMainSparsify.runBound enc branch bound x + workRegs er + 2 ∧
      Eval (procedure splitter).invoke steps caller
        (result splitter caller (enc x)
          (Encoding.encodeList enc
            (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves)) := by
  have ready' : SubexpMainSparsify.Ready (SubexpMainSparsify.mainPorts er es)
      ((SubexpMainSparsify.procedure splitter).project (resetResult caller)) := by
    constructor
    · intro i
      change (resetResult caller).stacks _ = []
      rw [reset_stacks]
      exact ready.1 i
    · change (resetResult caller).stacks _ = []
      rw [reset_stacks]
      exact ready.2
  have hbody' : (resetResult caller).stacks (persistent es 0) = enc x := by
    rw [reset_stacks]
    exact hbody
  obtain ⟨steps, hb, hs⟩ := SubexpMainSparsify.invoke_runs splitter (resetResult caller)
    ready' enc branch P cost bound x hx hbody' hclosed hreal hbound
  refine ⟨workRegs er + 1 + steps + 1, by omega, ?_⟩
  exact sequence_invoke _ _ (reset_invoke caller) hs

theorem leaf_stream (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (body leaves : List Bool) :
    (result splitter caller body leaves).stacks (persistent es 7) = leaves :=
  SubexpMainSparsify.installed_leaf_stream splitter (resetResult caller) body leaves

theorem preserves_persistent (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (body leaves : List Bool)
    (i : Fin 32) (h0 : i ≠ 0) (h7 : i ≠ 7) :
    (result splitter caller body leaves).stacks (persistent es i) =
      caller.stacks (persistent es i) := by
  rw [result, SubexpMainSparsify.installed_preserves_persistent splitter
    (resetResult caller) body leaves i h0 h7, reset_stacks]

theorem preserves_control (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (body leaves : List Bool) (i : Fin 3) :
    (result splitter caller body leaves).regs (controlRegister er i) =
      caller.regs (controlRegister er i) := by
  rw [result, Procedure.install_control, reset_control_register]

end SubexponentialSAT.SubexpCanonicalSparsify

end OAI.Algorithms
