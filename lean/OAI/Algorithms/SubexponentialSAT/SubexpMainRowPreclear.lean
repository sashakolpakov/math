import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram
import OAI.Algorithms.SubexponentialSAT.SubexpLayoutPorts
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowWorkspace

namespace OAI.Algorithms

/-!
# Physical preparation of the row evaluator's private workspace

Only the 79 agreed ordinary stack ports are cleared.  The selected words
may initially have arbitrary lengths.  The fixed local program uses sixteen
Boolean registers and 288 stacks and is embedded through LayoutPorts.
-/

namespace SubexponentialSAT.SubexpMainRowPreclear

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)

abbrev LocalData := State 16 288

abbrev Selected (j : ℕ) : Prop :=
  (22 ≤ j ∧ j ≤ 25) ∨ (30 ≤ j ∧ j ≤ 73) ∨ j = 75 ∨ j = 255 ∨
    (257 ≤ j ∧ j ≤ 263) ∨ (266 ≤ j ∧ j ≤ 287)

def ports : List (Fin 288) :=
  (List.finRange 288).filter (fun i => decide (Selected i.val))

theorem ports_nodup : ports.Nodup := (List.nodup_finRange 288).filter _

@[simp] theorem mem_ports (i : Fin 288) : i ∈ ports ↔ Selected i.val := by
  simp [ports]

@[simp] theorem ports_length : ports.length = 79 := by decide

theorem selected_lt {j : ℕ} (h : Selected j) : j < 288 := by
  dsimp [Selected] at h
  omega

theorem workspace_selected (i : Fin 49) :
    Selected (Subexp.UniversalRowWorkspace.port i).val := by
  rw [Subexp.UniversalRowWorkspace.port_val]
  split_ifs <;> dsimp [Selected] <;> omega

abbrev command : Cmd 16 288 := WorkspaceCleanupProgram.command 0 1 ports

def program := WorkspaceCleanupProgram.program (0 : Fin 16) 1 ports 0 0

def localResult (a : LocalData) : LocalData := WorkspaceCleanupProgram.finish 0 1 ports a

theorem command_eval (a : LocalData) :
    Eval command (WorkspaceCleanupProgram.cost ports a) a (localResult a) :=
  WorkspaceCleanupProgram.command_eval 0 1 ports ports_nodup a

theorem program_trace (a : LocalData) :
    Trace program (WorkspaceCleanupProgram.cost ports a + 1)
      (a.withPC (some program.entry)) ((localResult a).withPC none) :=
  WorkspaceCleanupProgram.program_trace 0 1 ports ports_nodup 0 0 a

theorem program_labels : size command + 1 = 238 := by
  rw [command, WorkspaceCleanupProgram.command_size, ports_length]

def stackMap {es : ℕ} (alloc : Allocation es) (i : Fin 288) : Fin (totalStacks es) :=
  ordinary alloc ⟨i.val, by omega⟩

@[simp] theorem stackMap_val {es : ℕ} (alloc : Allocation es) (i : Fin 288) :
    (stackMap alloc i).val = i.val := rfl

theorem stackMap_injective {es : ℕ} (alloc : Allocation es) :
    Function.Injective (stackMap alloc) := by
  intro i j h
  exact Fin.ext (congrArg (fun p : Fin (totalStacks es) => p.val) h)

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 288
  labels := size command + 1
  program := program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun p : Fin (workRegs er) => p.val) h)⟩
  stack := ⟨stackMap alloc, stackMap_injective alloc⟩

def selectedBits {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  (ports.map (fun i => (a.stacks (stackMap alloc i)).length)).sum

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  2 * selectedBits alloc a + 3 * 79 + 1

noncomputable def result {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) : MainState er es :=
  (procedure er alloc).install a (localResult ((procedure er alloc).project a))

/-- The exact source instruction count includes the compiled final halt. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    Eval (procedure er alloc).invoke (runtimeBound alloc a) a (result alloc a) := by
  have h := Procedure.invoke_trace (procedure er alloc) a _
    (program_trace ((procedure er alloc).project a))
  have htime : WorkspaceCleanupProgram.cost ports ((procedure er alloc).project a) + 1 =
      runtimeBound alloc a := by
    simp only [WorkspaceCleanupProgram.cost, ports_length, runtimeBound, selectedBits]
    apply congrArg (fun n ↦ 2 * n + 3 * 79 + 1)
    apply congrArg List.sum
    apply List.map_congr_left
    intro i _
    rfl
  simpa only [result] using (htime ▸ h)

theorem result_local_stack {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 288) :
    (result alloc a).stacks (stackMap alloc i) =
      if i ∈ ports then [] else a.stacks (stackMap alloc i) := by
  have h := embedState_stack (procedure er alloc).registerMap (procedure er alloc).stack a
    (localResult ((procedure er alloc).project a)) (procedure er alloc).stack.injective i
  change (result alloc a).stacks (stackMap alloc i) =
    (localResult ((procedure er alloc).project a)).stacks i at h
  exact h.trans (calc
    (localResult ((procedure er alloc).project a)).stacks i =
        if i ∈ ports then [] else ((procedure er alloc).project a).stacks i :=
      WorkspaceCleanupProgram.finish_stack (0 : Fin 16) (1 : Fin 16) ports
        ((procedure er alloc).project a) i
    _ = if i ∈ ports then [] else a.stacks (stackMap alloc i) := by rfl)

/-- An exact global frame statement, including ports outside the local bank. -/
theorem result_stack {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (j : Fin (totalStacks es)) :
    (result alloc a).stacks j = if Selected j.val then [] else a.stacks j := by
  by_cases hj : j.val < 288
  · let i : Fin 288 := ⟨j.val, hj⟩
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
    (j : Fin (totalStacks es)) (hj : 288 ≤ j.val) :
    (result alloc a).stacks j = a.stacks j :=
  result_frame alloc a j (fun h => (Nat.not_lt.mpr hj) (selected_lt h))

theorem result_workspace {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 49) :
    (result alloc a).stacks (stackMap alloc (Subexp.UniversalRowWorkspace.port i)) = [] :=
  result_cleared alloc a _ (workspace_selected i)

theorem result_source {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 10) :
    (result alloc a).stacks (ordinary alloc ⟨128 + i.val, by omega⟩) =
      a.stacks (ordinary alloc ⟨128 + i.val, by omega⟩) := by
  apply result_frame
  change ¬ Selected (128 + i.val)
  dsimp [Selected]
  omega

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
  change 288 ≤ workStacks es + i.val
  omega

theorem result_control {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 3) :
    (result alloc a).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control _ _ _ i

/-- The cleanup price is local even when unrelated retained stores are large. -/
theorem runtimeBound_eq {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    runtimeBound alloc a = 2 * selectedBits alloc a + 238 := by
  unfold runtimeBound
  omega

end SubexponentialSAT.SubexpMainRowPreclear

end OAI.Algorithms
