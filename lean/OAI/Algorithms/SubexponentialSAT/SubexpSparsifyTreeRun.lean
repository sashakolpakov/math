import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpBoundedSparsify

namespace OAI.Algorithms

/-! Execute the same canonical worklist with its actual finite-tree cost.
This separates unconditional execution from a later numerical bound on the
per-node costs. No uniform runtime premise is needed to establish the run. -/

namespace SubexponentialSAT.SubexpSparsifyTreeRun

open BitProgram StructuredCalls SubexpMainProgram SubexpProcedureCompose
open SubexpMainSparsify

def treeBound {α : Type*} (er : ℕ) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (cost : α → ℕ) (x : α) : ℕ :=
  15 * (enc x).length + ExecWorklistLoop.nodeWork enc branch (fun y => cost y + 1) x +
    6 * (Encoding.encodeList enc
      (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves).length +
    workRegs er + 44

theorem canonical_invoke {α : Type*} {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels) (caller : MainState er es)
    (ready : Ready (mainPorts er es) ((procedure splitter).project caller))
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (P : α → Prop) (cost : α → ℕ) (x : α) (hx : P x)
    (hbody : caller.stacks (persistent es 0) = enc x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.BoundedRealizesOn splitter
      (mainPorts er es).register (mainPorts er es).coreStack
      (workFrame (mainPorts er es) ((procedure splitter).project (resetResult caller)) (enc x))
      enc branch.split P cost) :
    ∃ steps, steps ≤ treeBound er enc branch cost x ∧
      Eval (SubexpCanonicalSparsify.procedure splitter).invoke steps caller
        (SubexpCanonicalSparsify.result splitter caller (enc x)
          (Encoding.encodeList enc
            (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves)) := by
  let p := mainPorts er es
  let d := (procedure splitter).project (resetResult caller)
  have hready : Ready p d := by
    constructor
    · intro i
      change (resetResult caller).stacks _ = []
      rw [reset_stacks]
      exact ready.1 i
    · change (resetResult caller).stacks _ = []
      rw [reset_stacks]
      exact ready.2
  have hdBody : d.stacks (p.stack 5) = enc x := by
    change (resetResult caller).stacks ((mainPorts er es).stack 5) = enc x
    rw [mainPorts_source, reset_stacks]
    exact hbody
  obtain ⟨n, hn, he⟩ := SubexpBoundedSparsify.command_run p splitter d
    (d.regs ∘ p.register) enc branch P cost x hx hclosed hreal
  have ht := compiled_halt_trace he (p.stack 5) (p.stack 6)
  have hd := data_ready p d hready
  rw [hdBody] at hd
  rw [hd] at ht
  have hc := Procedure.invoke_trace (procedure splitter) (resetResult caller) _ ht
  refine ⟨workRegs er + 1 + (n + 1) + 1, ?_, sequence_invoke _ _ (reset_invoke caller) hc⟩
  unfold treeBound
  omega

theorem treeBound_le {α : Type*} (er : ℕ) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop)
    (cost : α → ℕ) (bound : ℕ)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hbound : ∀ y, P y → cost y + ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound)
    (x : α) (hx : P x) :
    treeBound er enc branch cost x ≤ runBound enc branch bound x + workRegs er + 2 := by
  have hb : ∀ y, P y → (cost y + 1) +
      ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound + 1 := by
    intro y hy
    have := hbound y hy
    omega
  have hn := ExecWorklistLoop.nodeWork_le_visits enc branch P
    (fun y => cost y + 1) (bound + 1) hclosed hb x hx
  have hfour : bound + 1 + 3 = bound + 4 := by omega
  rw [hfour] at hn
  unfold treeBound runBound
  rw [ExecSparsifyWorklist.initial_run_visits]
  omega

end SubexponentialSAT.SubexpSparsifyTreeRun

end OAI.Algorithms
