import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyNodeTerminal
import OAI.Algorithms.SubexponentialSAT.ExecBranchController

namespace OAI.Algorithms

/-! The successful node return invokes both concrete child programs. -/

namespace SubexponentialSAT.ExecSparsifyNode

open BitProgram StructuredCalls

def childReg (i : Fin 15) : Fin 32 := Fin.castAdd 17 i
def childStack (k : ℕ) (i : Fin 23) : Fin (k + 39) := port k (Fin.castAdd 16 i)

theorem childReg_injective : Function.Injective childReg := Fin.castAdd_injective 15 17
theorem childStack_injective (k : ℕ) : Function.Injective (childStack k) :=
  (port_injective k).comp (Fin.castAdd_injective 23 16)

def callChildren (k : ℕ) : Code k :=
  .call (ProgramLinking.liftProgram ExecBranchController.program childReg (childStack k))

def branch (k : ℕ) : Code k :=
  .seq (prepare k) (.seq (callChildren k) (branchReturn k))

noncomputable def branchProduced {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) : Data k :=
  RegisterResetProgram.zeroed (embedState childReg (childStack k) (prepared a)
    (ExecBranchController.outputState (a.stacks (port k 0)) (a.stacks (port k 1))
      F selected H))

def branchCost {k : ℕ} (a : Data k) (F selected : List (List ℕ)) (H : List ℕ) : ℕ :=
  prepareCost a + 25000 * (ExecBranchController.volume F selected H) ^ 2 + 32

theorem prepared_child_ready {k : ℕ} (a : Data k)
    (h2 : a.stacks (port k 2) = []) (h3 : a.stacks (port k 3) = []) :
    ExecBranchController.Ready (projectState childReg (childStack k) (prepared a)) := by
  refine ⟨?_, ?_, ?_⟩
  · change (prepared a).stacks (port k 2) = []
    rw [prepared_frame a (port k 2) (Or.inl (by change (2 : ℕ) < 4; omega))]
    exact h2
  · change (prepared a).stacks (port k 3) = []
    rw [prepared_frame a (port k 3) (Or.inl (by change (3 : ℕ) < 4; omega))]
    exact h3
  · intro i
    apply prepared_transient
    change 7 ≤ 7 + i.val ∧ 7 + i.val < 37
    omega

/-- This is a trace of the actual preparation, two child programs, and full
register reset. The old pending and leaf lists are arbitrary. -/
theorem branch_eval {k : ℕ} (a : Data k) (F selected : List (List ℕ)) (H : List ℕ)
    (h2 : a.stacks (port k 2) = []) (h3 : a.stacks (port k 3) = [])
    (h4 : a.stacks (port k 4) = []) (h5 : a.stacks (port k 5) = [])
    (h6 : a.stacks (port k 6) = []) (h7 : a.stacks (port k 7) = [])
    (hF : a.stacks (port k 21) = ExecBranchController.formulaCode F)
    (hS : a.stacks (port k 18) = ExecBranchController.formulaCode selected)
    (hH : a.stacks (port k 13) = ExecBranchController.clauseCode H) :
    ∃ t ≤ branchCost a F selected H,
      Eval (branch k) t a (branchProduced a F selected H) := by
  let b := projectState childReg (childStack k) (prepared a)
  have hbF : b.stacks 4 = ExecBranchController.formulaCode F := by
    change (prepared a).stacks (port k 4) = _
    rw [prepared_parent, hF]
  have hbH : b.stacks 5 = ExecBranchController.clauseCode H := by
    change (prepared a).stacks (port k 5) = _
    rw [prepared_core, hH]
  have hbS : b.stacks 6 = ExecBranchController.formulaCode selected := by
    change (prepared a).stacks (port k 6) = _
    rw [prepared_family, hS]
  obtain ⟨n, hn, hrun⟩ := ExecBranchController.program_runsIn_from_state b F selected H
    hbF hbH hbS (prepared_child_ready a h2 h3)
  have hb0 : b.stacks 0 = a.stacks (port k 0) := by
    change (prepared a).stacks (port k 0) = _
    exact prepared_frame a (port k 0) (Or.inl (by change (0 : ℕ) < 4; omega))
  have hb1 : b.stacks 1 = a.stacks (port k 1) := by
    change (prepared a).stacks (port k 1) = _
    exact prepared_frame a (port k 1) (Or.inl (by change (1 : ℕ) < 4; omega))
  rw [hb0, hb1] at hrun
  have hcall := eval_call_from_state ExecBranchController.program childReg (childStack k)
    (prepared a) childReg_injective (childStack_injective k) hrun
  have hreset := branchReturn_eval (embedState childReg (childStack k) (prepared a)
    (ExecBranchController.outputState (a.stacks (port k 0)) (a.stacks (port k 1)) F selected H))
  refine ⟨prepareCost a + (n + 32), ?_, ?_⟩
  · unfold branchCost
    omega
  · exact (prepare_eval a h4 h5 h6 h7).seq (hcall.seq hreset)

theorem branchProduced_child_port {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) (i : Fin 23) :
    (branchProduced a F selected H).stacks (childStack k i) =
      (ExecBranchController.outputState (a.stacks (port k 0)) (a.stacks (port k 1))
        F selected H).stacks i :=
  embedState_stack childReg (childStack k) (prepared a) _ (childStack_injective k) i

@[simp] theorem branchProduced_pending {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) :
    (branchProduced a F selected H).stacks (port k 0) = a.stacks (port k 0) :=
  branchProduced_child_port a F selected H 0

@[simp] theorem branchProduced_leaves {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) :
    (branchProduced a F selected H).stacks (port k 1) = a.stacks (port k 1) :=
  branchProduced_child_port a F selected H 1

@[simp] theorem branchProduced_childA {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) :
    (branchProduced a F selected H).stacks (port k 2) =
      ExecWorklistProgram.record
        (ExecBranchController.formulaCode (ExecCoreChildProgram.result F selected H)) :=
  branchProduced_child_port a F selected H 2

@[simp] theorem branchProduced_childB {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) :
    (branchProduced a F selected H).stacks (port k 3) =
      ExecWorklistProgram.record
        (ExecBranchController.formulaCode (ExecPetalChildProgram.result F selected H)) :=
  branchProduced_child_port a F selected H 3

theorem branchProduced_stack_frame {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) (i : Fin (k + 39)) (hi : 23 ≤ i.val) :
    (branchProduced a F selected H).stacks i = (prepared a).stacks i := by
  apply embedState_stack_frame childReg (childStack k) (prepared a) _ i
  rintro ⟨j, hj⟩
  have he := congrArg Fin.val hj
  change j.val = i.val at he
  omega

theorem branchProduced_clean {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) (i : Fin (k + 39))
    (hi : 4 ≤ i.val ∧ i.val < 37) : (branchProduced a F selected H).stacks i = [] := by
  by_cases hj : i.val < 23
  · let j : Fin 23 := ⟨i.val, hj⟩
    have he : childStack k j = i := Fin.ext rfl
    rw [← he, branchProduced_child_port]
    exact ExecBranchController.outputState_clean _ _ F selected H j hi.1
  · rw [branchProduced_stack_frame a F selected H i (by omega)]
    exact prepared_transient a i (by omega)

theorem branchProduced_parameter {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) (i : Fin (k + 39)) (hi : 37 ≤ i.val) :
    (branchProduced a F selected H).stacks i = a.stacks i := by
  rw [branchProduced_stack_frame a F selected H i (by omega)]
  exact prepared_frame a i (Or.inr hi)

@[simp] theorem branchProduced_register {k : ℕ} (a : Data k)
    (F selected : List (List ℕ)) (H : List ℕ) (i : Fin 32) :
    (branchProduced a F selected H).regs i = false := rfl

def branchProgram (k : ℕ) := compiled (branch k) (port k 0) (port k 2)

theorem branchProgram_runsIn {k : ℕ} (a : Data k) (F selected : List (List ℕ)) (H : List ℕ)
    (h2 : a.stacks (port k 2) = []) (h3 : a.stacks (port k 3) = [])
    (h4 : a.stacks (port k 4) = []) (h5 : a.stacks (port k 5) = [])
    (h6 : a.stacks (port k 6) = []) (h7 : a.stacks (port k 7) = [])
    (hF : a.stacks (port k 21) = ExecBranchController.formulaCode F)
    (hS : a.stacks (port k 18) = ExecBranchController.formulaCode selected)
    (hH : a.stacks (port k 13) = ExecBranchController.clauseCode H) :
    RunsIn (branchProgram k) (branchCost a F selected H + 1)
      (a.withPC (some (branchProgram k).entry)) ((branchProduced a F selected H).withPC none) := by
  obtain ⟨t, ht, he⟩ := branch_eval a F selected H h2 h3 h4 h5 h6 h7 hF hS hH
  exact ⟨t + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he (port k 0) (port k 2)⟩

end SubexponentialSAT.ExecSparsifyNode

end OAI.Algorithms
