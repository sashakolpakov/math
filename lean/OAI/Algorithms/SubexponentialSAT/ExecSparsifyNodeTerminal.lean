import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyNode
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Concrete return paths for a sparsifier node

Every search stack is cleared on the terminal path, including the saved
witness. Both paths reset all thirty-two work registers. The terminal return
then writes the one decision bit consumed by the outer worklist.
-/

namespace SubexponentialSAT.ExecSparsifyNode

open BitProgram StructuredCalls

def searchPorts (k : ℕ) : List (Fin (k + 39)) :=
  (List.finRange 32).map (fun i => port k ⟨5 + i.val, by omega⟩)

theorem searchPorts_nodup (k : ℕ) : (searchPorts k).Nodup := by
  apply (List.nodup_finRange 32).map
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 5 + i.val = 5 + j.val at hv
  omega

@[simp] theorem searchPorts_length (k : ℕ) : (searchPorts k).length = 32 := by
  simp [searchPorts]

@[simp] theorem mem_searchPorts (k : ℕ) (i : Fin (k + 39)) :
    i ∈ searchPorts k ↔ 5 ≤ i.val ∧ i.val < 37 := by
  simp only [searchPorts, List.mem_map]
  constructor
  · rintro ⟨j, _, rfl⟩
    change 5 ≤ 5 + j.val ∧ 5 + j.val < 37
    omega
  · intro hi
    refine ⟨⟨i.val - 5, by omega⟩, List.mem_finRange _, ?_⟩
    apply Fin.ext
    change 5 + (i.val - 5) = i.val
    omega

def searchBits {k : ℕ} (a : Data k) : ℕ :=
  ((searchPorts k).map (fun i => (a.stacks i).length)).sum

def terminalReturn (k : ℕ) : Code k :=
  .seq (WorkspaceCleanupProgram.command 0 1 (searchPorts k))
    (.seq RegisterResetProgram.all (.base (.atom (.set 2 true))))

def terminalReturned {k : ℕ} (a : Data k) : Data k :=
  ⟨Function.update (fun _ => false) 2 true,
    fun i => if i ∈ searchPorts k then [] else a.stacks i⟩

def terminalCost {k : ℕ} (a : Data k) : ℕ := 2 * searchBits a + 129

/-- The cost counts all discarded search data, all register resets, and
the explicit terminal decision. It has no worklist-tail term. -/
theorem terminalReturn_eval {k : ℕ} (a : Data k) :
    Eval (terminalReturn k) (terminalCost a) a (terminalReturned a) := by
  let b := WorkspaceCleanupProgram.finish (0 : Fin 32) 1 (searchPorts k) a
  have hc := WorkspaceCleanupProgram.command_eval (0 : Fin 32) 1
    (searchPorts k) (searchPorts_nodup k) a
  have hr := RegisterResetProgram.all_eval b
  have hs : Eval (.base (.atom (.set (r := 32) (s := k + 39) 2 true))) 1
      (RegisterResetProgram.zeroed b) (terminalReturned a) := by
    exact .base (.atom _ _)
  have h := hc.seq (hr.seq hs)
  have hcost : WorkspaceCleanupProgram.cost (searchPorts k) a + (32 + 1) =
      terminalCost a := by
    simp [WorkspaceCleanupProgram.cost, terminalCost, searchBits]
  simpa only [terminalReturn, hcost] using h

@[simp] theorem terminalReturned_decision {k : ℕ} (a : Data k) :
    (terminalReturned a).regs 2 = true := by simp [terminalReturned]

theorem terminalReturned_other_register {k : ℕ} (a : Data k) (i : Fin 32)
    (hi : i ≠ 2) : (terminalReturned a).regs i = false := by
  simp [terminalReturned, hi]

theorem terminalReturned_clean {k : ℕ} (a : Data k) (i : Fin (k + 39))
    (hi : 5 ≤ i.val ∧ i.val < 37) : (terminalReturned a).stacks i = [] := by
  simp [terminalReturned, hi]

theorem terminalReturned_frame {k : ℕ} (a : Data k) (i : Fin (k + 39))
    (hi : i.val < 5 ∨ 37 ≤ i.val) :
    (terminalReturned a).stacks i = a.stacks i := by
  have hn : ¬ (5 ≤ i.val ∧ i.val < 37) := by omega
  simp [terminalReturned, hn]

/-- This final reset is also used after the child controller, whose own
fifteen-register reset does not cover the full search frame. -/
def branchReturn (k : ℕ) : Code k := RegisterResetProgram.all

theorem branchReturn_eval {k : ℕ} (a : Data k) :
    Eval (branchReturn k) 32 a (RegisterResetProgram.zeroed a) :=
  RegisterResetProgram.all_eval a

def terminalProgram (k : ℕ) := compiled (terminalReturn k) (port k 0) (port k 2)

theorem terminalProgram_trace {k : ℕ} (a : Data k) :
    Trace (terminalProgram k) (terminalCost a + 1)
      (a.withPC (some (terminalProgram k).entry)) ((terminalReturned a).withPC none) :=
  compiled_halt_trace (terminalReturn_eval a) (port k 0) (port k 2)

end SubexponentialSAT.ExecSparsifyNode

end OAI.Algorithms
