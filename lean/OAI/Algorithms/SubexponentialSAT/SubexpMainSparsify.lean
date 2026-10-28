import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.WorklistIOProgram
import OAI.Algorithms.SubexponentialSAT.ExecWorklistLoop
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram
import OAI.Algorithms.SubexponentialSAT.ProgramStateFrames

namespace OAI.Algorithms

/-!
# Physical input and output around the finite sparsification worklist

The formula body is preserved while an actual bit program constructs its
singleton pending list. The existing finite worklist then runs, and an actual
two-pass transfer moves its forward leaf stream to the caller's output port.
The splitter remains an explicit finite program with a measured trace contract;
no semantic splitting function is introduced as a machine instruction.
-/

namespace SubexponentialSAT.SubexpMainSparsify

open BitProgram StructuredCalls

structure Ports (r s : ℕ) where
  register : Fin 4 ↪ Fin r
  stack : Fin 7 ↪ Fin s

namespace Ports

variable {r s : ℕ}

def coreStack (p : Ports r s) (i : Fin 5) : Fin s := p.stack (i.castAdd 2)

theorem coreStack_injective (p : Ports r s) : Function.Injective p.coreStack := by
  intro i j h
  have he := p.stack.injective h
  exact Fin.ext (congrArg (fun a : Fin 7 => a.val) he)

end Ports

variable {r s : ℕ}

noncomputable def data (p : Ports r s) (frame : State r s)
    (regs : Fin 4 → Bool) (pending leaves body output : List Bool) : State r s :=
  embedState p.register p.stack frame
    (WorklistIOProgram.ioState regs pending leaves body output)

@[simp] theorem data_register (p : Ports r s) (frame : State r s)
    (regs : Fin 4 → Bool) (pending leaves body output : List Bool) (i : Fin 4) :
    (data p frame regs pending leaves body output).regs (p.register i) = regs i :=
  embedState_register p.register p.stack frame _ p.register.injective i

@[simp] theorem data_stack (p : Ports r s) (frame : State r s)
    (regs : Fin 4 → Bool) (pending leaves body output : List Bool) (i : Fin 7) :
    (data p frame regs pending leaves body output).stacks (p.stack i) =
      (WorklistIOProgram.ioState regs pending leaves body output).stacks i :=
  embedState_stack p.register p.stack frame _ p.stack.injective i

theorem data_register_frame (p : Ports r s) (frame : State r s)
    (regs : Fin 4 → Bool) (pending leaves body output : List Bool)
    (i : Fin r) (hi : ¬ ∃ j, p.register j = i) :
    (data p frame regs pending leaves body output).regs i = frame.regs i :=
  embedState_register_frame p.register p.stack frame _ i hi

theorem data_stack_frame (p : Ports r s) (frame : State r s)
    (regs : Fin 4 → Bool) (pending leaves body output : List Bool)
    (i : Fin s) (hi : ¬ ∃ j, p.stack j = i) :
    (data p frame regs pending leaves body output).stacks i = frame.stacks i :=
  embedState_stack_frame p.register p.stack frame _ i hi

theorem data_eq_self (p : Ports r s) (frame : State r s)
    (regs : Fin 4 → Bool) (pending leaves body output : List Bool)
    (hr : ∀ i, frame.regs (p.register i) = regs i)
    (hs : ∀ i, frame.stacks (p.stack i) =
      (WorklistIOProgram.ioState regs pending leaves body output).stacks i) :
    data p frame regs pending leaves body output = frame := by
  apply embedState_eq_of_ports p.register p.stack frame frame _
    p.register.injective p.stack.injective
  · exact hr
  · intro i hi; rfl
  · exact hs
  · intro i hi; rfl

def Ready (p : Ports r s) (d : State r s) : Prop :=
  (∀ i, d.stacks (p.coreStack i) = []) ∧ d.stacks (p.stack 6) = []

theorem data_ready (p : Ports r s) (d : State r s) (h : Ready p d) :
    data p d (d.regs ∘ p.register) [] [] (d.stacks (p.stack 5)) [] = d := by
  apply data_eq_self
  · intro i; rfl
  · intro i
    fin_cases i
    · exact h.1 0
    · exact h.1 1
    · exact h.1 2
    · exact h.1 3
    · exact h.1 4
    · rfl
    · exact h.2

/-- The invariant frame contains runtime thresholds and all caller data.
The core worklist ports are overwritten by its canonical state. -/
noncomputable def workFrame (p : Ports r s) (frame : State r s) (body : List Bool) :
    State r s := data p frame (fun _ => false) [] [] body []

theorem canonical_data {α : Type*} (p : Ports r s) (frame : State r s)
    (body : List Bool) (enc : α → List Bool) (state : ExecSparsifyWorklist.State α) :
    ExecWorklistLoop.Ambient.liftData p.register p.coreStack (workFrame p frame body)
      (ExecWorklistLoop.canonicalData enc state) =
    data p frame (fun _ => false) (Encoding.encodeList enc state.pending)
      (Encoding.encodeList enc state.leaves) body [] := by
  apply embedState_eq_of_ports p.register p.coreStack (workFrame p frame body) _ _
    p.register.injective p.coreStack_injective
  · intro i
    rw [data_register]
    fin_cases i <;> rfl
  · intro i hi
    rw [data_register_frame _ _ _ _ _ _ _ i hi]
    exact (data_register_frame _ _ _ _ _ _ _ i hi).symm
  · intro i
    change (data p frame (fun _ => false) _ _ body []).stacks (p.stack (i.castAdd 2)) = _
    rw [data_stack]
    fin_cases i <;> rfl
  · intro i hi
    by_cases hp : ∃ j, p.stack j = i
    · obtain ⟨j, rfl⟩ := hp
      change (data p frame (fun _ => false) _ _ body []).stacks (p.stack j) =
        (data p frame (fun _ => false) [] [] body []).stacks (p.stack j)
      rw [data_stack, data_stack]
      fin_cases j
      · exact False.elim (hi ⟨0, rfl⟩)
      · exact False.elim (hi ⟨1, rfl⟩)
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · rw [data_stack_frame _ _ _ _ _ _ _ i hp]
      exact (data_stack_frame _ _ _ _ _ _ _ i hp).symm

abbrev load (p : Ports r s) : Cmd r s :=
  liftCommand WorklistIOProgram.loader 5 0 p.register p.stack

abbrev unload (p : Ports r s) : Cmd r s :=
  liftCommand WorklistIOProgram.unloader 1 6 p.register p.stack

theorem load_eval (p : Ports r s) (frame : State r s)
    (regs : Fin 4 → Bool) (body : List Bool) :
    Eval (load p) (15 * body.length + 23)
      (data p frame regs [] [] body [])
      (data p frame (fun _ => false) (Encoding.encodeList id [body]) [false] body []) := by
  have h := eval_liftCommand (WorklistIOProgram.loader_eval regs body) 5 0
    p.register p.stack frame p.register.injective p.stack.injective
  convert h using 1
  · rfl
  · rw [show (fun _ : Fin 4 => false) = WorklistIOProgram.zeroRegs from rfl]
    rfl

theorem unload_eval (p : Ports r s) (frame : State r s) (body leaves : List Bool) :
    Eval (unload p) (6 * leaves.length + 12)
      (data p frame (fun _ => false) [false] leaves body [])
      (data p frame (fun _ => false) [] [] body leaves) := by
  have h := eval_liftCommand (WorklistIOProgram.unloader_eval body leaves) 1 6
    p.register p.stack frame p.register.injective p.stack.injective
  convert h using 1
  · rw [show (fun _ : Fin 4 => false) = WorklistIOProgram.zeroRegs from rfl]
    rfl
  · rw [show (fun _ : Fin 4 => false) = WorklistIOProgram.zeroRegs from rfl]
    rfl

abbrev command {labels : ℕ} (p : Ports r s) (splitter : Program r s labels) : Cmd r s :=
  .seq (load p) (.seq (.call (ExecWorklistLoop.Ambient.program splitter p.register p.coreStack))
    (unload p))

abbrev program {labels : ℕ} (p : Ports r s) (splitter : Program r s labels) :=
  compiled (command p splitter) (p.stack 5) (p.stack 6)

/-- The measured command returns the worklist's actual leaf sequence in its
forward serialized order. The preserved formula is not charged per node. -/
theorem command_eval {α : Type*} {labels : ℕ}
    (p : Ports r s) (splitter : Program r s labels) (frame : State r s)
    (regs : Fin 4 → Bool) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (x : α) (hx : P x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.RealizesOn splitter p.register p.coreStack
      (workFrame p frame (enc x)) enc branch.split P cost) :
    Eval (command p splitter)
      (15 * (enc x).length + 23 +
        (ExecWorklistLoop.nodeWork enc branch (fun y => cost y + 1) x + 6 +
          (6 * (Encoding.encodeList enc
            (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves).length + 12)))
      (data p frame regs [] [] (enc x) [])
      (data p frame (fun _ => false) [] [] (enc x)
        (Encoding.encodeList enc
          (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves)) := by
  have hi : ExecSparsifyWorklist.Invariant P (ExecSparsifyWorklist.initial x) := by
    simpa [ExecSparsifyWorklist.Invariant, ExecSparsifyWorklist.initial] using hx
  have ht := ExecWorklistLoop.Ambient.run_trace splitter p.register p.coreStack
    (workFrame p frame (enc x)) p.register.injective p.coreStack_injective
    enc branch P cost hreal hclosed (ExecSparsifyWorklist.initial x) hi
  rw [canonical_data, canonical_data] at ht
  have hs : Eval (.call (ExecWorklistLoop.Ambient.program splitter p.register p.coreStack))
      (ExecWorklistLoop.nodeWork enc branch (fun y => cost y + 1) x + 6)
      (data p frame (fun _ => false) (Encoding.encodeList id [enc x]) [false] (enc x) [])
      (data p frame (fun _ => false) [false]
        (Encoding.encodeList enc
          (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves) (enc x) []) := by
    apply Eval.call
    simpa only [ExecSparsifyWorklist.initial, ExecWorklistLoop.forestWork_cons,
      ExecWorklistLoop.forestWork_nil, Nat.add_zero, Encoding.encodeList,
      ExecSparsifyWorklist.run_pending_nil, id_eq] using ht
  exact (load_eval p frame regs (enc x)).seq (hs.seq (unload_eval p frame (enc x) _))

/-- An actual finite-table execution, with the local splitter bound needed
only on its preserved reachable-state invariant. -/
theorem program_runsIn {α : Type*} {labels : ℕ}
    (p : Ports r s) (splitter : Program r s labels) (frame : State r s)
    (regs : Fin 4 → Bool) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (bound : ℕ) (x : α) (hx : P x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.RealizesOn splitter p.register p.coreStack
      (workFrame p frame (enc x)) enc branch.split P cost)
    (hbound : ∀ y, P y → cost y + ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound) :
    RunsIn (program p splitter)
      (15 * (enc x).length + (bound + 4) *
        (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).visits +
        6 * (Encoding.encodeList enc
          (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves).length + 42)
      ((data p frame regs [] [] (enc x) []).withPC (some (program p splitter).entry))
      ((data p frame (fun _ => false) [] [] (enc x)
        (Encoding.encodeList enc
          (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves)).withPC none) := by
  have he := command_eval p splitter frame regs enc branch P cost x hx hclosed hreal
  have ht := compiled_halt_trace he (p.stack 5) (p.stack 6)
  refine ⟨_, ?_, ht⟩
  have hb : ∀ y, P y → (cost y + 1) +
      ExecWorklistLoop.updateCost enc y (branch.split y) ≤ bound + 1 := by
    intro y hy
    have := hbound y hy
    omega
  have hn := ExecWorklistLoop.nodeWork_le_visits enc branch P
    (fun y => cost y + 1) (bound + 1) hclosed hb x hx
  have hfour : bound + 1 + 3 = bound + 4 := by omega
  rw [hfour] at hn
  rw [ExecSparsifyWorklist.initial_run_visits]
  omega

/-- The bound counts the physical input loader, the actual finite worklist,
and the physical forward-output transfer. -/
def runBound {α : Type*} (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (bound : ℕ) (x : α) : ℕ :=
  15 * (enc x).length + (bound + 4) *
    (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).visits +
    6 * (Encoding.encodeList enc
      (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves).length + 42

theorem leaf_stream_length_le {α : Type*} (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (width : ℕ)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hwidth : ∀ y, P y → (enc y).length ≤ width) (x : α) (hx : P x) :
    (Encoding.encodeList enc
      (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).leaves).length ≤
      1 + (2 * width + 2) *
        (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).visits := by
  have hp := ExecSparsifyWorklist.initial_run_leaves_invariant branch P hclosed x hx
  have hs := Encoding.length_encodeList_upper enc _ width (fun y hy => hwidth y (hp y hy))
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _
    (ExecSparsifyWorklist.initial_run_leaves_length_le_visits branch x)) 1)

/-- The output pass is linear in the serialized leaves and is absorbed into
the same actual visit count when every reachable formula has bounded size. -/
theorem runBound_le {α : Type*} (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (bound width : ℕ)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hwidth : ∀ y, P y → (enc y).length ≤ width) (x : α) (hx : P x) :
    runBound enc branch bound x ≤ 15 * (enc x).length +
      (bound + 12 * width + 16) *
        (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).visits + 48 := by
  have hs := Nat.mul_le_mul_left 6 (leaf_stream_length_le enc branch P width hclosed hwidth x hx)
  calc
    runBound enc branch bound x ≤ 15 * (enc x).length + (bound + 4) *
        (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).visits +
        6 * (1 + (2 * width + 2) *
          (ExecSparsifyWorklist.run branch (ExecSparsifyWorklist.initial x)).visits) + 42 := by
      dsimp [runBound]
      omega
    _ = _ := by ring

theorem ready_runsIn {α : Type*} {labels : ℕ}
    (p : Ports r s) (splitter : Program r s labels) (frame : State r s)
    (ready : Ready p frame) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (bound : ℕ) (x : α) (hx : P x) (hbody : frame.stacks (p.stack 5) = enc x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.RealizesOn splitter p.register p.coreStack
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
  simpa only [hd, runBound] using h

theorem primitive_runsIn {α : Type*} {labels : ℕ}
    (p : Ports r s) (splitter : Program r s labels) (frame : State r s)
    (ready : Ready p frame) (enc : α → List Bool)
    (branch : ExecSparsifyWorklist.Branching α) (P : α → Prop) (cost : α → ℕ)
    (bound : ℕ) (x : α) (hx : P x) (hbody : frame.stacks (p.stack 5) = enc x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.RealizesOn splitter p.register p.coreStack
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

/-! ## Allocation inside the fixed top-level solver -/

open SubexpMainProgram

def mainStack (es : ℕ) (i : Fin 7) : Fin (totalStacks es) :=
  if h : i.val < 5 then ⟨i.val, by dsimp [totalStacks, workStacks]; omega⟩
  else if i.val = 5 then persistent es 0 else persistent es 7

theorem mainStack_val (es : ℕ) (i : Fin 7) :
    (mainStack es i).val =
      if i.val < 5 then i.val else if i.val = 5 then workStacks es else workStacks es + 7 := by
  unfold mainStack
  split_ifs <;> rfl

theorem mainStack_injective (es : ℕ) : Function.Injective (mainStack es) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg (fun a : Fin (totalStacks es) => a.val) h
  change (mainStack es i).val = (mainStack es j).val at hv
  rw [mainStack_val, mainStack_val] at hv
  split_ifs at hv <;> (try dsimp [workStacks] at hv) <;> omega

def mainPorts (er es : ℕ) : Ports (workRegs er) (totalStacks es) where
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun a : Fin (workRegs er) => a.val) h)⟩
  stack := ⟨mainStack es, mainStack_injective es⟩

@[simp] theorem mainPorts_source (er es : ℕ) :
    (mainPorts er es).stack 5 = persistent es 0 := by
  change mainStack es ⟨5, by decide⟩ = persistent es 0
  simp [mainStack]

@[simp] theorem mainPorts_output (er es : ℕ) :
    (mainPorts er es).stack 6 = persistent es 7 := by
  change mainStack es ⟨6, by decide⟩ = persistent es 7
  simp [mainStack]

theorem mainStack_not_persistent (es : ℕ) (i : Fin 32) (h0 : i ≠ 0) (h7 : i ≠ 7) :
    ¬ ∃ j, mainStack es j = persistent es i := by
  rintro ⟨j, hj⟩
  have hv := congrArg (fun a : Fin (totalStacks es) => a.val) hj
  change (mainStack es j).val = (persistent es i).val at hv
  rw [mainStack_val] at hv
  change (if j.val < 5 then j.val else if j.val = 5 then workStacks es else workStacks es + 7) =
    workStacks es + i.val at hv
  split_ifs at hv with hsmall hfive
  · dsimp [workStacks] at hv
    omega
  · apply h0
    apply Fin.ext
    change i.val = 0
    omega
  · apply h7
    apply Fin.ext
    change i.val = 7
    omega

/-- The source program may use all fixed work registers. The Procedure
embedding keeps the outer record-iterator control bits separate. -/
abbrev procedure {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels) : Procedure er es where
  registers := workRegs er
  stackCount := totalStacks es
  labels := size (command (mainPorts er es) splitter) + 1
  program := program (mainPorts er es) splitter
  register := Function.Embedding.refl _
  stack := Function.Embedding.refl _

theorem main_data_preserves_persistent (er es : ℕ)
    (frame : State (workRegs er) (totalStacks es)) (regs : Fin 4 → Bool)
    (pending leaves body output : List Bool) (i : Fin 32) (h0 : i ≠ 0) (h7 : i ≠ 7) :
    (data (mainPorts er es) frame regs pending leaves body output).stacks (persistent es i) =
      frame.stacks (persistent es i) :=
  data_stack_frame _ _ _ _ _ _ _ _ (mainStack_not_persistent es i h0 h7)

/-- The concrete wrapper as a top-level Procedure call. The source and target
are genuine caller states, including its unchanged iterator-control bits. -/
theorem invoke_runs {α : Type*} {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es)
    (ready : Ready (mainPorts er es) ((procedure splitter).project caller))
    (enc : α → List Bool) (branch : ExecSparsifyWorklist.Branching α)
    (P : α → Prop) (cost : α → ℕ) (bound : ℕ) (x : α) (hx : P x)
    (hbody : caller.stacks (persistent es 0) = enc x)
    (hclosed : ExecSparsifyWorklist.SplitClosed branch.split P)
    (hreal : ExecWorklistLoop.Ambient.RealizesOn splitter
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
    change caller.stacks (persistent es 0) = enc x
    exact hbody
  obtain ⟨steps, hsteps, ht⟩ := ready_runsIn (mainPorts er es) splitter
    ((procedure splitter).project caller) ready enc branch P cost bound x hx hbody'
    hclosed hreal hbound
  exact ⟨steps, hsteps, Procedure.invoke_trace (procedure splitter) caller _ ht⟩

theorem installed_leaf_stream {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (body leaves : List Bool) :
    ((procedure splitter).install caller
      (data (mainPorts er es) ((procedure splitter).project caller) (fun _ => false)
        [] [] body leaves)).stacks (persistent es 7) = leaves := by
  have h := embedState_stack (procedure splitter).registerMap (procedure splitter).stack
    caller (data (mainPorts er es) ((procedure splitter).project caller) (fun _ => false)
      [] [] body leaves) (procedure splitter).stack.injective (persistent es 7)
  change _ = (data (mainPorts er es) ((procedure splitter).project caller) (fun _ => false)
    [] [] body leaves).stacks (persistent es 7) at h
  refine h.trans ?_
  rw [← mainPorts_output er es, data_stack]
  rfl

theorem installed_preserves_persistent {er es labels : ℕ}
    (splitter : Program (workRegs er) (totalStacks es) labels)
    (caller : MainState er es) (body leaves : List Bool)
    (i : Fin 32) (h0 : i ≠ 0) (h7 : i ≠ 7) :
    ((procedure splitter).install caller
      (data (mainPorts er es) ((procedure splitter).project caller) (fun _ => false)
        [] [] body leaves)).stacks (persistent es i) = caller.stacks (persistent es i) := by
  have h := embedState_stack (procedure splitter).registerMap (procedure splitter).stack
    caller (data (mainPorts er es) ((procedure splitter).project caller) (fun _ => false)
      [] [] body leaves) (procedure splitter).stack.injective (persistent es i)
  change _ = (data (mainPorts er es) ((procedure splitter).project caller) (fun _ => false)
    [] [] body leaves).stacks (persistent es i) at h
  refine h.trans ?_
  rw [main_data_preserves_persistent er es _ _ _ _ _ _ i h0 h7]
  rfl

end SubexponentialSAT.SubexpMainSparsify

end OAI.Algorithms
