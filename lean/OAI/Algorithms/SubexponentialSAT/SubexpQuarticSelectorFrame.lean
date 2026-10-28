import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpQuarticSelectorControl
import OAI.Algorithms.SubexponentialSAT.SubexpMainProgram

namespace OAI.Algorithms

/-! The fixed selector allocation and its exact frame in Main storage. -/

namespace SubexponentialSAT.SubexpQuarticSelectorFrame

open BitProgram StructuredCalls SubexpMainProgram

def lowPort (es : ℕ) (i : Fin 36) : Fin (totalStacks es) :=
  ⟨i.val, by dsimp [totalStacks, workStacks]; omega⟩

def stackMap (es : ℕ) : Fin 38 → Fin (totalStacks es) :=
  Fin.addCases (m := 35) (n := 3) (motive := fun _ => Fin (totalStacks es))
    (fun i => lowPort es (i.castAdd 1)) ![persistent es 6, persistent es 15, lowPort es 35]

theorem stackMap_low (es : ℕ) (i : Fin 35) :
    stackMap es (i.castAdd 3) = lowPort es (i.castAdd 1) :=
  Fin.addCases_left (m := 35) (n := 3) (motive := fun _ => Fin (totalStacks es))
    (left := fun j => lowPort es (j.castAdd 1))
    (right := ![persistent es 6, persistent es 15, lowPort es 35]) i

theorem low_ne_persistent (es : ℕ) (i : Fin 36) (j : Fin 32) :
    lowPort es i ≠ persistent es j := by
  intro h
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
  simp only [lowPort, persistent, Fin.val_natAdd] at hv
  dsimp [workStacks] at hv
  omega

theorem stackMap_injective (es : ℕ) : Function.Injective (stackMap es) := by
  intro i
  refine Fin.addCases (m := 35) (n := 3) (fun a => ?_) (fun a => ?_) i
  · intro j
    refine Fin.addCases (m := 35) (n := 3) (fun b => ?_) (fun b => ?_) j
    · intro h
      apply Fin.ext
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      simpa only [stackMap, Fin.addCases_left, lowPort, Fin.val_castAdd] using hv
    · intro h
      exfalso
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      fin_cases b <;> simp [stackMap, lowPort, persistent, workStacks,
        Fin.addCases, Fin.coe_ofNat_eq_mod] at hv <;> omega
  · intro j
    refine Fin.addCases (m := 35) (n := 3) (fun b => ?_) (fun b => ?_) j
    · intro h
      exfalso
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      fin_cases a <;> simp [stackMap, lowPort, persistent, workStacks,
        Fin.addCases, Fin.coe_ofNat_eq_mod] at hv <;> omega
    · intro h
      have hv := congrArg (fun q : Fin (totalStacks es) => q.val) h
      fin_cases a <;> fin_cases b <;> first
      | rfl
      | (simp [stackMap, lowPort, persistent, workStacks,
          Fin.addCases, Fin.coe_ofNat_eq_mod] at hv <;> omega)

def procedure (er es : ℕ) : Procedure er es where
  registers := 14
  stackCount := 38
  labels := size SubexpQuarticSelectorControl.command + 1
  program := SubexpQuarticSelectorControl.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := ⟨stackMap es, stackMap_injective es⟩

def WorkspaceReady {er es : ℕ} (a : MainState er es) : Prop :=
  ∀ i : Fin 36, a.stacks (lowPort es i) = []

theorem project_stack {er es : ℕ} (a : MainState er es) (i : Fin 38) :
    ((procedure er es).project a).stacks i = a.stacks (stackMap es i) := rfl

theorem ready_low (regs : Fin 14 → Bool) (prime output : List Bool) (i : Fin 35) :
    (SubexpQuarticSelectorControl.ready regs prime output).stacks (i.castAdd 3) = [] :=
  Fin.addCases_left (m := 35) (n := 3) (motive := fun _ => List Bool)
    (left := fun _ => []) (right := ![prime, output, []]) i

theorem project_ready {er es : ℕ} (a : MainState er es) (ha : WorkspaceReady a) :
    (procedure er es).project a = SubexpQuarticSelectorControl.ready
      (a.regs ∘ (procedure er es).registerMap)
      (a.stacks (persistent es 6)) (a.stacks (persistent es 15)) := by
  apply SubexpScanPrimitives.state_ext
  · rfl
  · funext i
    refine Fin.addCases (m := 35) (n := 3) (fun j => ?_) (fun j => ?_) i
    · rw [project_stack, stackMap_low, ha, ready_low]
    · fin_cases j
      · rfl
      · rfl
      · rw [project_stack]
        change a.stacks (lowPort es 35) = []
        exact ha 35

/-- This is a proof description of the actual final state, not executable
selection code. The finite program is `procedure.program`. -/
noncomputable def result {er es : ℕ} (a : MainState er es) (output : List Bool) :
    MainState er es :=
  (procedure er es).install a (SubexpQuarticSelectorControl.ready (fun _ => false)
    (a.stacks (persistent es 6)) output)

theorem result_stacks {er es : ℕ} (a : MainState er es) (output : List Bool)
    (ha : WorkspaceReady a) :
    (result a output).stacks = Function.update a.stacks (persistent es 15) output := by
  let out := SubexpQuarticSelectorControl.ready (fun _ => false)
    (a.stacks (persistent es 6)) output
  have hlocal (i : Fin 38) : out.stacks i =
      (Function.update a.stacks (persistent es 15) output) (stackMap es i) := by
    refine Fin.addCases (m := 35) (n := 3) (fun j => ?_) (fun j => ?_) i
    · rw [stackMap_low]
      simpa only [out, SubexpQuarticSelectorControl.ready,
        SubexpQuarticSelectorControl.extendState, Fin.addCases_left,
        Function.update_of_ne (low_ne_persistent es (j.castAdd 1) 15)] using
        (ha (j.castAdd 1)).symm
    · fin_cases j
      · simp [out, SubexpQuarticSelectorControl.ready,
          SubexpQuarticSelectorControl.extendState, stackMap, Fin.addCases,
          Fin.coe_ofNat_eq_mod, (persistent_injective es).eq_iff]
      · simp [out, SubexpQuarticSelectorControl.ready,
          SubexpQuarticSelectorControl.extendState, stackMap, Fin.addCases,
          Fin.coe_ofNat_eq_mod]
      · simpa [out, SubexpQuarticSelectorControl.ready,
          SubexpQuarticSelectorControl.extendState, stackMap, Fin.addCases,
          Fin.coe_ofNat_eq_mod, low_ne_persistent] using (ha 35).symm
  funext i
  by_cases hi : ∃ j, stackMap es j = i
  · obtain ⟨j, rfl⟩ := hi
    exact (embedState_stack (procedure er es).registerMap (procedure er es).stack
      a out (procedure er es).stack.injective j).trans (hlocal j)
  · have h15 : i ≠ persistent es 15 := by
      rintro rfl
      exact hi ⟨36, rfl⟩
    rw [Function.update_of_ne h15]
    exact embedState_stack_frame (procedure er es).registerMap (procedure er es).stack
      a out i hi

theorem result_register {er es : ℕ} (a : MainState er es) (output : List Bool)
    (i : Fin 14) : (result a output).regs ((procedure er es).registerMap i) = false :=
  embedState_register (procedure er es).registerMap (procedure er es).stack a _
    (procedure er es).registerMap_injective i

theorem result_register_frame {er es : ℕ} (a : MainState er es) (output : List Bool)
    (i : Fin (totalRegs er)) (hi : ¬ ∃ j, (procedure er es).registerMap j = i) :
    (result a output).regs i = a.regs i :=
  embedState_register_frame (procedure er es).registerMap (procedure er es).stack a _ i hi

theorem result_control {er es : ℕ} (a : MainState er es) (output : List Bool)
    (i : Fin 3) : (result a output).regs (controlRegister er i) = a.regs (controlRegister er i) :=
  Procedure.install_control (procedure er es) a _ i

end SubexponentialSAT.SubexpQuarticSelectorFrame

end OAI.Algorithms
