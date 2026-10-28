import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpCanonicalSparsify
import OAI.Algorithms.SubexponentialSAT.ExecWorklistLoopBounded

namespace OAI.Algorithms

/-!
# Main sparsification with bounded actual node executions

This module keeps the already compiled loader, worklist, unloader and full
register reset. Only the proof interface changes: a node's actual execution
may finish before its local upper bound and may take different times in
different framed states. Every premise still refers to the same fixed finite
splitter program and its actual measured executions.
-/

namespace SubexponentialSAT.SubexpBoundedSparsify

open BitProgram StructuredCalls SubexpMainSparsify

variable {r s : ℕ}

theorem command_run {α : Type*} {labels : ℕ}
    (p : Ports r s) (splitter : Program r s labels) (frame : State r s)
    (regs : Fin 4 → Bool) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (x : α) (hx : P x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.BoundedRealizesOn splitter p.register p.coreStack
      (workFrame p frame (enc x)) enc branch.split P cost) :
    ∃ steps, steps ≤ 15 * (enc x).length + 23 +
        (ExecWorklistLoop.nodeWork enc branch (fun y => cost y + 1) x + 6 +
          (6 * (Encoding.encodeList enc
            (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves).length + 12)) ∧
      Eval (command p splitter) steps
        (data p frame regs [] [] (enc x) [])
        (data p frame (fun _ => false) [] [] (enc x)
          (Encoding.encodeList enc
            (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves)) := by
  have hi : ExecSparsifyWorklist.Invariant P (ExecSparsifyWorklist.initial x) := by
    simpa [ExecSparsifyWorklist.Invariant, ExecSparsifyWorklist.initial] using hx
  obtain ⟨n, hn, ht⟩ := ExecWorklistLoop.Ambient.run_bounded splitter p.register p.coreStack
    (workFrame p frame (enc x)) p.register.injective p.coreStack_injective
    enc branch P cost hreal hclosed (ExecSparsifyWorklist.initial x) hi
  rw [canonical_data, canonical_data] at ht
  have hn' : n ≤ ExecWorklistLoop.nodeWork enc branch (fun y => cost y + 1) x + 6 := by
    simpa only [ExecSparsifyWorklist.initial, ExecWorklistLoop.forestWork_cons,
      ExecWorklistLoop.forestWork_nil, Nat.add_zero] using hn
  have hs : Eval (.call (ExecWorklistLoop.Ambient.program splitter p.register p.coreStack)) n
      (data p frame (fun _ => false) (Encoding.encodeList id [enc x]) [false] (enc x) [])
      (data p frame (fun _ => false) [false]
        (Encoding.encodeList enc
          (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves) (enc x) []) := by
    apply Eval.call
    simpa only [ExecSparsifyWorklist.initial, Encoding.encodeList,
      ExecSparsifyWorklist.run_pending_nil, id_eq] using ht
  exact ⟨_, by omega,
    (load_eval p frame regs (enc x)).seq (hs.seq (unload_eval p frame (enc x) _))⟩

theorem program_runsIn {α : Type*} {labels : ℕ}
    (p : Ports r s) (splitter : Program r s labels) (frame : State r s)
    (regs : Fin 4 → Bool) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (bound : ℕ) (x : α) (hx : P x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.BoundedRealizesOn splitter p.register p.coreStack
      (workFrame p frame (enc x)) enc branch.split P cost)
    (hbound : ∀ y, P y → cost y + ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound) :
    RunsIn (program p splitter) (runBound enc branch bound x)
      ((data p frame regs [] [] (enc x) []).withPC (some (program p splitter).entry))
      ((data p frame (fun _ => false) [] [] (enc x)
        (Encoding.encodeList enc
          (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves)).withPC none) := by
  obtain ⟨steps, hsteps, he⟩ := command_run p splitter frame regs enc branch P cost x hx hclosed hreal
  refine ⟨steps + 1, ?_, compiled_halt_trace he (p.stack 5) (p.stack 6)⟩
  have hb : ∀ y, P y → (cost y + 1) +
      ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound + 1 := by
    intro y hy
    have := hbound y hy
    omega
  have hn := ExecWorklistLoop.nodeWork_le_visits enc branch P
    (fun y => cost y + 1) (bound + 1) hclosed hb x hx
  have hfour : bound + 1 + 3 = bound + 4 := by omega
  rw [hfour] at hn
  unfold runBound
  rw [ExecSparsifyWorklist.initial_run_visits]
  omega

theorem ready_runsIn {α : Type*} {labels : ℕ}
    (p : Ports r s) (splitter : Program r s labels) (frame : State r s)
    (ready : Ready p frame) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (bound : ℕ) (x : α) (hx : P x) (hbody : frame.stacks (p.stack 5) = enc x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.BoundedRealizesOn splitter p.register p.coreStack
      (workFrame p frame (enc x)) enc branch.split P cost)
    (hbound : ∀ y, P y → cost y + ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound) :
    RunsIn (program p splitter) (runBound enc branch bound x)
      (frame.withPC (some (program p splitter).entry))
      ((data p frame (fun _ => false) [] [] (enc x)
        (Encoding.encodeList enc
          (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves)).withPC none) := by
  have h := program_runsIn p splitter frame (frame.regs ∘ p.register)
    enc branch P cost bound x hx hclosed hreal hbound
  have hd := data_ready p frame ready
  rw [hbody] at hd
  simpa only [hd] using h

theorem primitive_runsIn {α : Type*} {labels : ℕ}
    (p : Ports r s) (splitter : Program r s labels) (frame : State r s)
    (ready : Ready p frame) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (bound : ℕ) (x : α) (hx : P x) (hbody : frame.stacks (p.stack 5) = enc x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.BoundedRealizesOn splitter p.register p.coreStack
      (workFrame p frame (enc x)) enc branch.split P cost)
    (hbound : ∀ y, P y → cost y + ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound) :
    Computation.RunsIn (primitive (program p splitter)).step
      (primitiveOverhead (program p splitter) * runBound enc branch bound x)
      (primitiveCfg (program p splitter) (frame.withPC (some (program p splitter).entry)))
      (primitiveCfg (program p splitter)
        ((data p frame (fun _ => false) [] [] (enc x)
          (Encoding.encodeList enc
            (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves)).withPC none)) :=
  BitProgram.primitive_execution _
    (ready_runsIn p splitter frame ready enc branch P cost bound x hx hbody hclosed hreal hbound)

open SubexpMainProgram

theorem invoke_runs {α : Type*} {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es)
    (ready : Ready (mainPorts er es) ((procedure splitter).project caller))
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (P : α → Prop) (cost : α → ℕ) (bound : ℕ) (x : α) (hx : P x)
    (hbody : caller.stacks (persistent es 0) = enc x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.BoundedRealizesOn splitter
      (mainPorts er es).register (mainPorts er es).coreStack
      (workFrame (mainPorts er es) ((procedure splitter).project caller) (enc x))
      enc branch.split P cost)
    (hbound : ∀ y, P y → cost y + ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound) :
    ∃ steps, steps ≤ runBound enc branch bound x ∧
      Eval (procedure splitter).invoke steps caller
        ((procedure splitter).install caller
          (data (mainPorts er es) ((procedure splitter).project caller) (fun _ => false)
            [] [] (enc x) (Encoding.encodeList enc
              (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves))) := by
  have hbody' : ((procedure splitter).project caller).stacks ((mainPorts er es).stack 5) = enc x := by
    change caller.stacks ((mainPorts er es).stack 5) = enc x
    simpa only [mainPorts_source] using hbody
  obtain ⟨steps, hsteps, ht⟩ := ready_runsIn (mainPorts er es) splitter
    ((procedure splitter).project caller) ready enc branch P cost bound x hx hbody'
    hclosed hreal hbound
  exact ⟨steps, hsteps, Procedure.invoke_trace (procedure splitter) caller _ ht⟩

open SubexpProcedureCompose

/-- Full physical register initialization followed by the unchanged actual
worklist. The bounded splitter restores the canonical post-reset frame. -/
theorem canonical_invoke {α : Type*} {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels) (caller : MainState er es)
    (ready : Ready (mainPorts er es) ((procedure splitter).project caller))
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (P : α → Prop) (cost : α → ℕ) (bound : ℕ) (x : α) (hx : P x)
    (hbody : caller.stacks (persistent es 0) = enc x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.BoundedRealizesOn splitter
      (mainPorts er es).register (mainPorts er es).coreStack
      (workFrame (mainPorts er es) ((procedure splitter).project (resetResult caller)) (enc x))
      enc branch.split P cost)
    (hbound : ∀ y, P y → cost y + ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound) :
    ∃ steps, steps ≤ runBound enc branch bound x + workRegs er + 2 ∧
      Eval (SubexpCanonicalSparsify.procedure splitter).invoke steps caller
        (SubexpCanonicalSparsify.result splitter caller (enc x)
          (Encoding.encodeList enc
            (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves)) := by
  have ready' : Ready (mainPorts er es) ((procedure splitter).project (resetResult caller)) := by
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
  obtain ⟨steps, hb, hs⟩ := invoke_runs splitter (resetResult caller)
    ready' enc branch P cost bound x hx hbody' hclosed hreal hbound
  exact ⟨workRegs er + 1 + steps + 1, by omega,
    sequence_invoke _ _ (reset_invoke caller) hs⟩

end SubexponentialSAT.SubexpBoundedSparsify

end OAI.Algorithms
