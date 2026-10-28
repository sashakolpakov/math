import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainLocalBasisPorts
import OAI.Algorithms.SubexponentialSAT.SubexpLocalBasisReady

namespace OAI.Algorithms

/-! The exact Main-storage frame for the native batch wrapper. -/

namespace SubexponentialSAT.SubexpMainLocalBasisFrame

open BitProgram StructuredCalls SubexpMainProgram SubexpLayoutPorts
open SubexpMainLocalBasisPorts

def project {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) : State 32 131 :=
  ⟨a.regs ∘ registerMap er hr, a.stacks ∘ stackMap alloc⟩

def WorkspaceReady {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) : Prop :=
  SubexpLocalBasisReady.WorkspaceReady (project alloc hr a)

def context {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) : SubexpLocalBasisState.Context :=
  SubexpLocalBasisReady.context (project alloc hr a)

theorem project_ready {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (ha : WorkspaceReady alloc hr a) :
    project alloc hr a = SubexpLocalBasisState.ready (context alloc hr a)
      (a.regs ∘ registerMap er hr) (a.stacks (persistent es 25))
      (a.stacks (master alloc 14)) :=
  SubexpLocalBasisReady.ready_context (project alloc hr a) ha

/-- Proof description of the endpoint. The executable wrapper is defined
separately by concrete counter, batch, and cleanup instructions. -/
noncomputable def result {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) : MainState er es :=
  embedState (registerMap er hr) (stackMap alloc) a
    (SubexpLocalBasisState.result (context alloc hr a) (a.stacks (persistent es 25)) output)

theorem result_stacks {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (ha : WorkspaceReady alloc hr a) :
    (result alloc hr a output).stacks =
      Function.update (Function.update a.stacks (ordinary alloc 111) []) (master alloc 14) output := by
  let out := SubexpLocalBasisState.result (context alloc hr a) (a.stacks (persistent es 25)) output
  have hs : out.stacks =
      Function.update (Function.update (project alloc hr a).stacks 111 []) 127 output := by
    rw [SubexpLocalBasisReady.result_stacks (context alloc hr a)
      (a.regs ∘ registerMap er hr) (a.stacks (persistent es 25))
      (a.stacks (master alloc 14)) output, ← project_ready alloc hr a ha]
  have hlocal (j : Fin 131) : out.stacks j =
      (Function.update (Function.update a.stacks (stackMap alloc 111) [])
        (stackMap alloc 127) output) (stackMap alloc j) := by
    rw [hs]
    simp only [Function.update_apply, (stackMap_injective alloc).eq_iff,
      project, Function.comp_apply]
  funext i
  by_cases hi : ∃ j, stackMap alloc j = i
  · obtain ⟨j, rfl⟩ := hi
    exact (embedState_stack (registerMap er hr) (stackMap alloc) a out
      (stackMap_injective alloc) j).trans (hlocal j)
  · have h111 : i ≠ stackMap alloc 111 := by
      intro h
      exact hi ⟨111, h.symm⟩
    have h127 : i ≠ stackMap alloc 127 := by
      intro h
      exact hi ⟨127, h.symm⟩
    rw [show ordinary alloc 111 = stackMap alloc 111 from rfl,
      show master alloc 14 = stackMap alloc 127 from rfl,
      Function.update_of_ne h127, Function.update_of_ne h111]
    exact embedState_stack_frame (registerMap er hr) (stackMap alloc) a out i hi

theorem result_register {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (i : Fin 32) :
    (result alloc hr a output).regs (registerMap er hr i) = false :=
  embedState_register (registerMap er hr) (stackMap alloc) a _
    (registerMap_injective er hr) i

theorem result_register_frame {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (i : Fin (totalRegs er))
    (hi : ¬ ∃ j, registerMap er hr j = i) :
    (result alloc hr a output).regs i = a.regs i :=
  embedState_register_frame (registerMap er hr) (stackMap alloc) a _ i hi

theorem result_control {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (i : Fin 3) :
    (result alloc hr a output).regs (controlRegister er i) = a.regs (controlRegister er i) := by
  apply result_register_frame
  rintro ⟨j, hj⟩
  exact work_ne_control er (registers er hr j) i hj

theorem result_preserved {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (ha : WorkspaceReady alloc hr a)
    (i : Fin (totalStacks es)) (h111 : i ≠ ordinary alloc 111) (hout : i ≠ master alloc 14) :
    (result alloc hr a output).stacks i = a.stacks i := by
  rw [result_stacks alloc hr a output ha,
    Function.update_of_ne hout, Function.update_of_ne h111]

theorem result_output {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (ha : WorkspaceReady alloc hr a) :
    (result alloc hr a output).stacks (master alloc 14) = output := by
  rw [result_stacks alloc hr a output ha]
  simp

theorem result_workspace {er es : ℕ} (alloc : Allocation es) (hr : 16 ≤ er)
    (a : MainState er es) (output : List Bool) (ha : WorkspaceReady alloc hr a) :
    WorkspaceReady alloc hr (result alloc hr a output) := by
  intro i hi
  change (result alloc hr a output).stacks (stackMap alloc i) = []
  have h111 : i ≠ 111 := by intro h; subst i; exact hi (by decide)
  have h127 : i ≠ 127 := by intro h; subst i; exact hi (by decide)
  rw [result_preserved alloc hr a output ha (stackMap alloc i)
    (by simpa only [← stackMap_length] using
      fun h => h111 ((stackMap_injective alloc) h))
    (by simpa only [← stackMap_output] using
      fun h => h127 ((stackMap_injective alloc) h))]
  exact ha i hi

end SubexponentialSAT.SubexpMainLocalBasisFrame

end OAI.Algorithms
