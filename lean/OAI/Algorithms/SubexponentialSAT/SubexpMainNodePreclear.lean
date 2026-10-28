import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts

namespace OAI.Algorithms

/-!
# Physical preparation of the node worker's workspace

This fixed sixteen-register/320-stack program clears exactly 307 ordinary
ports.  It retains the source context, the R+1 counter, the row word, and
the framed target-node stream.  Its cost depends on the bits it removes.
-/

namespace SubexponentialSAT.SubexpMainNodePreclear

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)

abbrev LocalData := State 16 320

abbrev Selected (j : ℕ) : Prop :=
  j < 320 ∧ ¬ (128 ≤ j ∧ j ≤ 137) ∧ j ≠ 243 ∧ j ≠ 255 ∧ j ≠ 300

def ports : List (Fin 320) :=
  (List.finRange 320).filter (fun i => decide (Selected i.val))

theorem ports_nodup : ports.Nodup := (List.nodup_finRange 320).filter _

@[simp] theorem mem_ports (i : Fin 320) : i ∈ ports ↔ Selected i.val := by
  constructor
  · intro h
    exact of_decide_eq_true (List.mem_filter.mp h).2
  · intro h
    exact List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true h⟩

private theorem filter_length_split {S : Type} (f : S → Bool) (n : ℕ) (xs : List S) :
    (xs.filter f).length = ((xs.take n).filter f).length + ((xs.drop n).filter f).length := by
  rw [← List.length_append, ← List.filter_append, List.take_append_drop]

@[simp] theorem ports_length : ports.length = 307 := by
  let xs := List.finRange 320
  let f := fun i : Fin 320 ↦ decide (Selected i.val)
  change (xs.filter f).length = 307
  rw [filter_length_split f 64 xs,
    filter_length_split f 64 (xs.drop 64),
    filter_length_split f 64 ((xs.drop 64).drop 64),
    filter_length_split f 64 (((xs.drop 64).drop 64).drop 64)]
  have h₀ : ((xs.take 64).filter f).length = 64 := by decide
  have h₁ : (((xs.drop 64).take 64).filter f).length = 64 := by decide
  have h₂ : ((((xs.drop 64).drop 64).take 64).filter f).length = 54 := by decide
  have h₃ : (((((xs.drop 64).drop 64).drop 64).take 64).filter f).length = 62 := by
    decide
  have h₄ : (((((xs.drop 64).drop 64).drop 64).drop 64).filter f).length = 63 := by
    decide
  omega

theorem selected_lt {j : ℕ} (h : Selected j) : j < 320 := h.1

def command : Cmd 16 320 := WorkspaceCleanupProgram.command 0 1 ports

def localResult (a : LocalData) : LocalData := WorkspaceCleanupProgram.finish 0 1 ports a

theorem command_eval (a : LocalData) :
    Eval command (WorkspaceCleanupProgram.cost ports a) a (localResult a) :=
  WorkspaceCleanupProgram.command_eval 0 1 ports ports_nodup a

structure LocalProgram where
  labels : ℕ
  code : Program 16 320 labels
  trace : ∀ a : LocalData,
    Trace code (WorkspaceCleanupProgram.cost ports a + 1)
      (a.withPC (some code.entry)) ((localResult a).withPC none)

def localProgram : LocalProgram where
  labels := size (WorkspaceCleanupProgram.command (0 : Fin 16) 1 ports) + 1
  code := WorkspaceCleanupProgram.program (0 : Fin 16) 1 ports 0 0
  trace := WorkspaceCleanupProgram.program_trace 0 1 ports ports_nodup 0 0

theorem program_labels : size command + 1 = 922 := by
  rw [command, WorkspaceCleanupProgram.command_size, ports_length]

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 320) : Fin (totalStacks es) :=
  ordinary alloc ⟨i.val, by omega⟩

@[simp] theorem stackMap_val {es : ℕ} (alloc : Allocation es) (i : Fin 320) :
    (stackMap alloc i).val = i.val := rfl

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  exact Fin.ext (congrArg (fun p : Fin (totalStacks es) => p.val) h)

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 320
  labels := localProgram.labels
  program := localProgram.code
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun p : Fin (workRegs er) => p.val) h)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def selectedBits {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  (ports.map (fun i => (a.stacks (stackMap alloc i)).length)).sum

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  2 * selectedBits alloc a + 3 * 307 + 1

noncomputable def result {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) : MainState er es :=
  (procedure er alloc).install a (localResult ((procedure er alloc).project a))

/-- The exact source instruction count includes the compiled final halt. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    Eval (procedure er alloc).invoke (runtimeBound alloc a) a (result alloc a) := by
  have h := Procedure.invoke_trace (procedure er alloc) a _
    (localProgram.trace ((procedure er alloc).project a))
  have hstack (i : Fin 320) :
      ((procedure er alloc).project a).stacks i = a.stacks (stackMap alloc i) := rfl
  have hcost : WorkspaceCleanupProgram.cost ports ((procedure er alloc).project a) + 1 =
      runtimeBound alloc a := by
    simp only [WorkspaceCleanupProgram.cost, ports_length, runtimeBound, selectedBits, hstack]
  rw [← hcost]
  change Eval (procedure er alloc).invoke
    (WorkspaceCleanupProgram.cost ports ((procedure er alloc).project a) + 1) a
    ((procedure er alloc).install a (localResult ((procedure er alloc).project a)))
  exact h

theorem result_local_stack {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 320) :
    (result alloc a).stacks (stackMap alloc i) =
      if i ∈ ports then [] else a.stacks (stackMap alloc i) := by
  have h := embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
    (localResult ((procedure er alloc).project a)) (procedure er alloc).stack.injective i
  change (result alloc a).stacks (stackMap alloc i) =
    if i ∈ ports then [] else ((procedure er alloc).project a).stacks i at h
  have hstack : ((procedure er alloc).project a).stacks i = a.stacks (stackMap alloc i) := rfl
  rw [hstack] at h
  exact h

/-- An exact global frame statement, including ports outside the local bank. -/
theorem result_stack {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (j : Fin (totalStacks es)) :
    (result alloc a).stacks j = if Selected j.val then [] else a.stacks j := by
  by_cases hj : j.val < 320
  · let i : Fin 320 := ⟨j.val, hj⟩
    have he : stackMap alloc i = j := Fin.ext rfl
    have h := result_local_stack alloc a i
    rw [he] at h
    simpa only [mem_ports] using h
  · have hm : ¬ ∃ i, (procedure er alloc).stack i = j := by
      rintro ⟨i, hi⟩
      have hv := congrArg (fun p : Fin (totalStacks es) => p.val) hi
      change i.val = j.val at hv
      exact hj (hv ▸ i.isLt)
    have hs : ¬ Selected j.val := fun h => hj (selected_lt h)
    have h := embedState_stack_frame (procedure er alloc).registerMap
      (procedure er alloc).stack a (localResult ((procedure er alloc).project a)) j hm
    simpa only [result, Procedure.install, ite_eq_right hs] using h

theorem result_cleared {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (j : Fin (totalStacks es)) (hj : Selected j.val) :
    (result alloc a).stacks j = [] := by
  rw [result_stack, ite_eq_left hj]

theorem result_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (j : Fin (totalStacks es)) (hj : ¬ Selected j.val) :
    (result alloc a).stacks j = a.stacks j := by
  rw [result_stack, ite_eq_right hj]

theorem result_high_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (j : Fin (totalStacks es)) (hj : 320 ≤ j.val) :
    (result alloc a).stacks j = a.stacks j :=
  result_frame alloc a j (fun h => (Nat.not_lt.mpr hj) (selected_lt h))

theorem result_source {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 10) :
    (result alloc a).stacks (ordinary alloc ⟨128 + i.val, by omega⟩) =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) := by
  apply result_frame
  change ¬ Selected (128 + i.val)
  dsimp [Selected]
  omega

theorem result_counter {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (result alloc a).stacks (ordinary alloc 243) = a.stacks (ordinary alloc 243) := by
  apply result_frame
  change ¬ Selected 243
  decide

theorem result_row {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (result alloc a).stacks (ordinary alloc 255) = a.stacks (ordinary alloc 255) := by
  apply result_frame
  change ¬ Selected 255
  decide

theorem result_nodes {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (result alloc a).stacks (ordinary alloc 300) = a.stacks (ordinary alloc 300) := by
  apply result_frame
  change ¬ Selected 300
  decide

theorem result_master {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 32) :
    (result alloc a).stacks (master alloc i) = a.stacks (master alloc i) := by
  apply result_high_frame
  rw [SubexpLayoutPorts.master_val]
  omega

theorem result_persistent {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 32) :
    (result alloc a).stacks (persistent es i) = a.stacks (persistent es i) := by
  apply result_high_frame
  have hw := alloc.enough.trans alloc.within
  change 320 ≤ workStacks es + i.val
  omega

theorem result_control {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 3) :
    (result alloc a).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control _ _ _ i

/-- Retained source tables and persistent stores are not part of this cost. -/
theorem runtimeBound_eq {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    runtimeBound alloc a = 2 * selectedBits alloc a + 922 := by
  unfold runtimeBound
  omega

end SubexponentialSAT.SubexpMainNodePreclear

end OAI.Algorithms
