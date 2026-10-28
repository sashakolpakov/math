import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainFinalize

namespace OAI.Algorithms

/-!
# Physical storage readiness after a leaf

The existing decoder and stack cleanup are followed by the actual finite
work-register reset program. These are storage facts, not an assumed semantic
layout contract. The main controller's final leaf cleanup is checked separately.
-/

namespace SubexponentialSAT.SubexpMainReady

open StructuredCalls SubexpMainProgram

variable {er es : ℕ}

def procedure (er es count : ℕ) (hcount : count ≤ workStacks es) : Procedure er es :=
  SubexpProcedureCompose.sequence (SubexpMainFinalize.procedure er es count hcount)
    (SubexpProcedureCompose.resetWorkRegisters er es)

noncomputable def result (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    MainState er es :=
  SubexpProcedureCompose.resetResult
    (SubexpMainFinalize.finalData count hcount a regs modulus width word)

def StorageReady (count : ℕ) (a : MainState er es) : Prop :=
  (∀ i : Fin (workRegs er), a.regs (workRegister er i) = false) ∧
    ∀ i : Fin (totalStacks es), i.val < count → a.stacks i = []

theorem selectedBits_eq_zero (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (ha : StorageReady count a) :
    WorkspaceCleanupProgram.Main.selectedBits count hcount a = 0 := by
  unfold WorkspaceCleanupProgram.Main.selectedBits
  apply List.sum_eq_zero
  intro n hn
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hn
  have hil : i.val < count := (WorkspaceCleanupProgram.mem_prefixPorts _ _ i).mp hi
  rw [ha.2 i hil]
  rfl

theorem selectedBits_after_eval (count : ℕ) (hcount : count ≤ workStacks es)
    {cmd : MainCmd er es} {steps : ℕ} {a b : MainState er es}
    (h : Eval cmd steps a b) :
    WorkspaceCleanupProgram.Main.selectedBits count hcount b ≤
      WorkspaceCleanupProgram.Main.selectedBits count hcount a + steps := by
  have ht := compiled_trace h (persistent es 0) (persistent es 0)
  exact BitProgram.trace_listStackBits _
    (WorkspaceCleanupProgram.Main.selectedPorts es count hcount)
    (WorkspaceCleanupProgram.prefixPorts_nodup _ _) ht

theorem workspace_ne_persistent {count : ℕ} (hcount : count ≤ workStacks es)
    (i : Fin (totalStacks es)) (hi : i.val < count) (j : Fin 32) :
    i ≠ persistent es j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val = workStacks es + j.val at hv
  omega

/-- The parser writes protected control registers and persistent payload
ports, so it preserves the next layout call's ordinary storage readiness. -/
theorem leafInput_ready (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (tail bits : List Bool) (ha : StorageReady count a) :
    StorageReady count (leafInput a tail bits) := by
  constructor
  · intro i
    have h0 := work_ne_control er i (0 : Fin 3)
    have h1 := work_ne_control er i (1 : Fin 3)
    have h2 := work_ne_control er i (2 : Fin 3)
    simpa [leafInput, RecordPrograms.state, ports, h0, h1, h2] using ha.1 i
  · intro i hi
    have h7 := workspace_ne_persistent hcount i hi (7 : Fin 32)
    have h8 := workspace_ne_persistent hcount i hi (8 : Fin 32)
    simpa [leafInput, RecordPrograms.state, ports, h7, h8] using ha.2 i hi

theorem transferred_ready (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (ha : StorageReady count a) :
    StorageReady count (transferredData a) := by
  constructor
  · intro i
    by_cases hv : workRegister er i = scratchValue er <;>
      by_cases hp : workRegister er i = scratchPresent er <;>
      simp [transferredData, BitProgram.readRegs, Function.update_apply, hv, hp, ha.1 i]
  · intro i hi
    have h8 := workspace_ne_persistent hcount i hi (8 : Fin 32)
    have h9 := workspace_ne_persistent hcount i hi (9 : Fin 32)
    simpa [transferredData, StackRoutines.transferStacks, h8, h9] using ha.2 i hi

theorem result_stacks (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (result count hcount a regs modulus width word).stacks =
      (SubexpMainFinalize.finalData count hcount a regs modulus width word).stacks :=
  SubexpProcedureCompose.reset_stacks _

theorem result_work_register (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool)
    (i : Fin (workRegs er)) :
    (result count hcount a regs modulus width word).regs (workRegister er i) = false :=
  SubexpProcedureCompose.reset_work_register _ i

theorem result_cleared (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool)
    (i : Fin (totalStacks es)) (hi : i.val < count) :
    (result count hcount a regs modulus width word).stacks i = [] := by
  rw [result_stacks]
  exact WorkspaceCleanupProgram.Main.result_cleared count hcount _ i hi

theorem result_ready (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    StorageReady count (result count hcount a regs modulus width word) :=
  ⟨result_work_register count hcount a regs modulus width word,
    result_cleared count hcount a regs modulus width word⟩

theorem result_control (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) (i : Fin 3) :
    (result count hcount a regs modulus width word).regs (controlRegister er i) =
      a.regs (controlRegister er i) := by
  unfold result
  rw [SubexpProcedureCompose.reset_control_register]
  unfold SubexpMainFinalize.finalData
  rw [WorkspaceCleanupProgram.Main.result_control]
  exact Procedure.install_control _ _ _ i

theorem result_persistent_frame (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool)
    (i : Fin 32) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13) :
    (result count hcount a regs modulus width word).stacks (persistent es i) =
      a.stacks (persistent es i) := by
  rw [result_stacks]
  unfold SubexpMainFinalize.finalData
  rw [WorkspaceCleanupProgram.Main.result_persistent]
  exact SubexpMainDecode.installed_frame a _ i h10 h12 h13

theorem result_threshold (count : ℕ) (hcount : count ≤ workStacks es) (h8 : 8 ≤ count)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool)
    (i : Fin (totalStacks es)) (hi : count ≤ i.val) (hwork : i.val < workStacks es) :
    (result count hcount a regs modulus width word).stacks i = a.stacks i := by
  rw [result_stacks]
  exact SubexpMainFinalize.finalData_workspace_frame count hcount a regs modulus width word i
    (h8.trans hi) hi hwork

theorem result_modulus (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (result count hcount a regs modulus width word).stacks (persistent es 12) = modulus := by
  rw [result_stacks]
  unfold SubexpMainFinalize.finalData
  rw [WorkspaceCleanupProgram.Main.result_persistent]
  exact embedState_stack (SubexpMainDecode.procedure er es).registerMap
    (SubexpMainDecode.procedure er es).stack a (SubexpMainDecode.localResult regs modulus width word)
    (SubexpMainDecode.procedure er es).stack.injective (5 : Fin 8)

theorem result_width (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (result count hcount a regs modulus width word).stacks (persistent es 13) = width := by
  rw [result_stacks]
  unfold SubexpMainFinalize.finalData
  rw [WorkspaceCleanupProgram.Main.result_persistent]
  exact embedState_stack (SubexpMainDecode.procedure er es).registerMap
    (SubexpMainDecode.procedure er es).stack a (SubexpMainDecode.localResult regs modulus width word)
    (SubexpMainDecode.procedure er es).stack.injective (7 : Fin 8)

theorem result_answer (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    ((result count hcount a regs modulus width word).stacks (persistent es 10)).head? =
      some (SubexpDecodeProgram.answer modulus word) := by
  rw [result_stacks]
  unfold SubexpMainFinalize.finalData
  rw [WorkspaceCleanupProgram.Main.result_persistent]
  exact SubexpMainDecode.installed_head a regs modulus width word

theorem result_output (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (result count hcount a regs modulus width word).stacks (persistent es 10) =
      SubexpFlatCount.output modulus word := by
  rw [result_stacks]
  unfold SubexpMainFinalize.finalData
  rw [WorkspaceCleanupProgram.Main.result_persistent]
  exact embedState_stack (SubexpMainDecode.procedure er es).registerMap
    (SubexpMainDecode.procedure er es).stack a (SubexpMainDecode.localResult regs modulus width word)
    (SubexpMainDecode.procedure er es).stack.injective (0 : Fin 8)

theorem input_modulus (a : MainState er es) (regs : Fin 8 → Bool)
    (modulus width input : List Bool)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width input) :
    a.stacks (persistent es 12) = modulus :=
  congrArg (fun d => d.stacks (5 : Fin 8)) ready

theorem input_width (a : MainState er es) (regs : Fin 8 → Bool)
    (modulus width input : List Bool)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width input) :
    a.stacks (persistent es 13) = width :=
  congrArg (fun d => d.stacks (7 : Fin 8)) ready

/-- Register reset is an actual second procedure call, with its own halt and
the real final halt of sequential composition included in the bound. This
coarse bound counts all stored bits; `execution_selected` and
`execution_after_prefix` give bounds suitable for arbitrary pending streams. -/
theorem execution {B : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (hB : 0 < B) (P : List (SubexpFlatCount.Code B)) (a : MainState er es)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width (SubexpFlatCount.flatPolynomial P)) :
    ∃ (steps : ℕ) (finalRegs : Fin 8 → Bool),
      steps ≤ 3 * SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial P) +
        2 * BitProgram.stackBits a.stacks + 3 * count + workRegs er + 4 ∧
      Eval (procedure er es count hcount).invoke steps a
        (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) ∧
      StorageReady count
        (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) := by
  obtain ⟨n, finalRegs, hn, he, _, _, _⟩ :=
    SubexpMainFinalize.execution count hcount hB P a regs modulus width hwidth ready
  have hreset := SubexpProcedureCompose.reset_invoke
    (SubexpMainFinalize.finalData count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P))
  have hseq := SubexpProcedureCompose.sequence_invoke _ _ he hreset
  refine ⟨n + (workRegs er + 1) + 1, finalRegs, by omega, hseq, result_ready _ _ _ _ _ _ _⟩

/-- The pending stream and protected threshold bank do not contribute to
this bound: only selected workspace lengths are charged on entry. -/
theorem execution_selected {B : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (hB : 0 < B) (P : List (SubexpFlatCount.Code B)) (a : MainState er es)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width (SubexpFlatCount.flatPolynomial P)) :
    ∃ (steps : ℕ) (finalRegs : Fin 8 → Bool),
      steps ≤ 3 * SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial P) +
        2 * WorkspaceCleanupProgram.Main.selectedBits count hcount a +
        3 * count + workRegs er + 4 ∧
      Eval (procedure er es count hcount).invoke steps a
        (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) ∧
      StorageReady count
        (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) := by
  obtain ⟨n, finalRegs, hn, he, _, _, _⟩ :=
    SubexpMainFinalize.execution_selected count hcount hB P a regs modulus width hwidth ready
  have hreset := SubexpProcedureCompose.reset_invoke
    (SubexpMainFinalize.finalData count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P))
  have hseq := SubexpProcedureCompose.sequence_invoke _ _ he hreset
  refine ⟨n + (workRegs er + 1) + 1, finalRegs, by omega, hseq, result_ready _ _ _ _ _ _ _⟩

theorem execution_from_empty {B : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (hB : 0 < B) (P : List (SubexpFlatCount.Code B)) (a : MainState er es)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B)
    (storage : StorageReady count a)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width (SubexpFlatCount.flatPolynomial P)) :
    ∃ (steps : ℕ) (finalRegs : Fin 8 → Bool),
      steps ≤ 3 * SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial P) +
        3 * count + workRegs er + 4 ∧
      Eval (procedure er es count hcount).invoke steps a
        (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) ∧
      StorageReady count
        (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) := by
  obtain ⟨n, finalRegs, hn, he, hs⟩ :=
    execution_selected count hcount hB P a regs modulus width hwidth ready
  refine ⟨n, finalRegs, ?_, he, hs⟩
  simpa [selectedBits_eq_zero count hcount a storage] using hn

/-- Earlier phases are charged through their actual execution trace. Starting
with ready workspace makes the cleanup overhead independent of framed data. -/
theorem execution_after_prefix {B : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (hB : 0 < B) (P : List (SubexpFlatCount.Code B))
    (phase : MainCmd er es) (prefixSteps : ℕ) (start a : MainState er es)
    (storage : StorageReady count start) (hprefix : Eval phase prefixSteps start a)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width (SubexpFlatCount.flatPolynomial P)) :
    ∃ (steps : ℕ) (finalRegs : Fin 8 → Bool),
      steps ≤ 3 * (prefixSteps +
        SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial P)) +
        3 * count + workRegs er + 4 ∧
      Eval (.seq phase (procedure er es count hcount).invoke) steps start
        (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) ∧
      StorageReady count
        (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) := by
  have hbits := selectedBits_after_eval count hcount hprefix
  rw [selectedBits_eq_zero count hcount start storage] at hbits
  obtain ⟨n, finalRegs, hn, he, hs⟩ :=
    execution_selected count hcount hB P a regs modulus width hwidth ready
  exact ⟨prefixSteps + n, finalRegs, by omega, .seq hprefix he, hs⟩

/-- The main leaf epilogue changes only the two reusable persistent stacks. -/
theorem finished_stack_frame (a : MainState er es) (i : Fin (totalStacks es))
    (h9 : i ≠ persistent es 9) (h10 : i ≠ persistent es 10) :
    (finishedData a).stacks i = a.stacks i := by
  simp [finishedData, poppedAnswer, clearedData, StackRoutines.clearStacks,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, BitProgram.execInstr, h9, h10]

theorem finished_work_zero (a : MainState er es)
    (hz : ∀ i : Fin (workRegs er), a.regs (workRegister er i) = false) :
    ∀ i : Fin (workRegs er), (finishedData a).regs (workRegister er i) = false := by
  intro i
  have h0 := work_ne_control er i (0 : Fin 3)
  have h1 := work_ne_control er i (1 : Fin 3)
  have h2 := work_ne_control er i (2 : Fin 3)
  have hv1 := (control_ne_scratchValue er (1 : Fin 3)).symm
  have hp1 := (control_ne_scratchPresent er (1 : Fin 3)).symm
  by_cases hv : workRegister er i = scratchValue er <;>
    by_cases hp : workRegister er i = scratchPresent er <;>
    simp [finishedData, poppedAnswer, clearedData, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg,
      BitProgram.execInstr, BitProgram.readRegs, Function.update_apply,
      h0, h1, h2, hv1, hp1, hv, hp, hz i]

theorem finished_ready (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    StorageReady count (finishedData (result count hcount a regs modulus width word)) := by
  refine ⟨finished_work_zero _ (result_work_register count hcount a regs modulus width word), ?_⟩
  intro i hi
  have h9 : i ≠ persistent es 9 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = workStacks es + 9 at hv
    omega
  have h10 : i ≠ persistent es 10 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = workStacks es + 10 at hv
    omega
  rw [finished_stack_frame _ i h9 h10]
  exact result_cleared count hcount a regs modulus width word i hi

theorem finished_threshold (count : ℕ) (hcount : count ≤ workStacks es) (h8 : 8 ≤ count)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool)
    (i : Fin (totalStacks es)) (hi : count ≤ i.val) (hwork : i.val < workStacks es) :
    (finishedData (result count hcount a regs modulus width word)).stacks i = a.stacks i := by
  have h9 : i ≠ persistent es 9 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = workStacks es + 9 at hv
    omega
  have h10 : i ≠ persistent es 10 := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = workStacks es + 10 at hv
    omega
  rw [finished_stack_frame _ i h9 h10]
  exact result_threshold count hcount h8 a regs modulus width word i hi hwork

theorem finished_pending (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (finishedData (result count hcount a regs modulus width word)).stacks (persistent es 7) =
      a.stacks (persistent es 7) := by
  rw [finished_source]
  exact result_persistent_frame count hcount a regs modulus width word 7
    (by decide) (by decide) (by decide)

theorem finished_payload (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (finishedData (result count hcount a regs modulus width word)).stacks (persistent es 8) =
      a.stacks (persistent es 8) := by
  rw [SubexpMainProgram.finished_payload]
  exact result_persistent_frame count hcount a regs modulus width word 8
    (by decide) (by decide) (by decide)

theorem finished_modulus (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (finishedData (result count hcount a regs modulus width word)).stacks (persistent es 12) = modulus := by
  rw [finished_stack_frame _ _ (by simp) (by simp)]
  exact result_modulus count hcount a regs modulus width word

theorem finished_width (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (finishedData (result count hcount a regs modulus width word)).stacks (persistent es 13) = width := by
  rw [finished_stack_frame _ _ (by simp) (by simp)]
  exact result_width count hcount a regs modulus width word

theorem finished_reusable (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (finishedData (result count hcount a regs modulus width word)).stacks (persistent es 9) = [] ∧
    (finishedData (result count hcount a regs modulus width word)).stacks (persistent es 10) = [] :=
  ⟨finished_leaf _, finished_answer _⟩

theorem finished_found (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (finishedData (result count hcount a regs modulus width word)).regs (controlRegister er 2) =
      SubexpDecodeProgram.answer modulus word := by
  rw [SubexpMainProgram.finished_found, result_answer]
  rfl

theorem finished_modulus_preserved (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (startRegs finalRegs : Fin 8 → Bool)
    (modulus width input word : List Bool)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start startRegs modulus width input) :
    (finishedData (result count hcount a finalRegs modulus width word)).stacks (persistent es 12) =
      a.stacks (persistent es 12) := by
  rw [finished_modulus]
  exact (input_modulus a startRegs modulus width input ready).symm

theorem finished_width_preserved (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (startRegs finalRegs : Fin 8 → Bool)
    (modulus width input word : List Bool)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start startRegs modulus width input) :
    (finishedData (result count hcount a finalRegs modulus width word)).stacks (persistent es 13) =
      a.stacks (persistent es 13) := by
  rw [finished_width]
  exact (input_width a startRegs modulus width input ready).symm

theorem finished_persistent_preserved (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (startRegs finalRegs : Fin 8 → Bool)
    (modulus width input word : List Bool)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start startRegs modulus width input)
    (i : Fin 32) (h9 : i ≠ 9) (h10 : i ≠ 10) :
    (finishedData (result count hcount a finalRegs modulus width word)).stacks (persistent es i) =
      a.stacks (persistent es i) := by
  by_cases h12 : i = 12
  · subst i
    exact finished_modulus_preserved count hcount a startRegs finalRegs modulus width input word ready
  by_cases h13 : i = 13
  · subst i
    exact finished_width_preserved count hcount a startRegs finalRegs modulus width input word ready
  rw [finished_stack_frame _ _ (fun h => h9 (persistent_injective es h))
    (fun h => h10 (persistent_injective es h))]
  exact result_persistent_frame count hcount a finalRegs modulus width word i h10 h12 h13

theorem finished_controls (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    (finishedData (result count hcount a regs modulus width word)).regs (controlRegister er 0) = false ∧
    (finishedData (result count hcount a regs modulus width word)).regs (controlRegister er 1) = true ∧
    (finishedData (result count hcount a regs modulus width word)).regs (controlRegister er 2) =
      SubexpDecodeProgram.answer modulus word :=
  ⟨SubexpMainProgram.finished_tag _, SubexpMainProgram.finished_present _, finished_found _ _ _ _ _ _ _⟩

theorem finishCost_eq (a : MainState er es) :
    finishCost a = 2 * (a.stacks (persistent es 9)).length +
      2 * (a.stacks (persistent es 10)).tail.length + 9 := by
  simp [finishCost, clearCost, poppedAnswer, clearedData, StackRoutines.clearStacks,
    StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, BitProgram.execInstr,
    Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  omega

theorem finishCost_result (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    finishCost (result count hcount a regs modulus width word) =
      2 * (a.stacks (persistent es 9)).length +
      2 * (PositiveWordProgram.residual (ModularArithmetic.reduce modulus word)).length + 9 := by
  rw [finishCost_eq, result_output,
    result_persistent_frame count hcount a regs modulus width word 9
      (by decide) (by decide) (by decide)]
  rfl

private theorem residual_length_le (bits : List Bool) :
    (PositiveWordProgram.residual bits).length ≤ bits.length := by
  induction bits with
  | nil => simp [PositiveWordProgram.residual]
  | cons b bits ih =>
      cases b with
      | false =>
          simp only [PositiveWordProgram.residual, List.length_cons]
          omega
      | true => simp [PositiveWordProgram.residual]

theorem finishCost_result_le {B : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (P : List (SubexpFlatCount.Code B)) (a : MainState er es)
    (regs : Fin 8 → Bool) (modulus width : List Bool) :
    finishCost (result count hcount a regs modulus width (SubexpFlatCount.firstWord P)) ≤
      2 * (a.stacks (persistent es 9)).length + 2 * (modulus.length + B) + 9 := by
  rw [finishCost_result]
  have hres := residual_length_le (ModularArithmetic.reduce modulus (SubexpFlatCount.firstWord P))
  rw [ModularArithmetic.reduce_length] at hres
  have hw := SubexpFlatCount.firstWord_length_le P
  omega

/-- The complete physical decoder and epilogue execute to a reusable storage
state. The epilogue's actual clearing cost is retained explicitly. -/
theorem finished_execution {B : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (hB : 0 < B) (P : List (SubexpFlatCount.Code B)) (a : MainState er es)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width (SubexpFlatCount.flatPolynomial P)) :
    ∃ (steps : ℕ) (finalRegs : Fin 8 → Bool),
      steps ≤ 3 * SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial P) +
        2 * WorkspaceCleanupProgram.Main.selectedBits count hcount a +
        3 * count + workRegs er + 4 +
        finishCost (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) ∧
      Eval (.seq (procedure er es count hcount).invoke (finishLeaf er es)) steps a
        (finishedData (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P))) ∧
      StorageReady count
        (finishedData (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P))) ∧
      (finishedData (result count hcount a finalRegs modulus width
        (SubexpFlatCount.firstWord P))).regs (controlRegister er 2) =
          SubexpDecodeProgram.answer modulus (SubexpFlatCount.firstWord P) := by
  obtain ⟨n, finalRegs, hn, he, _⟩ :=
    execution_selected count hcount hB P a regs modulus width hwidth ready
  refine ⟨n + finishCost (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)),
    finalRegs, Nat.add_le_add_right hn _, .seq he (finishLeaf_eval _), ?_, ?_⟩
  · exact finished_ready count hcount a finalRegs modulus width _
  · exact finished_found count hcount a finalRegs modulus width _

/-- The complete prefix, decoder, and leaf epilogue have a bound independent
of the unread pending stream and protected threshold contents. The current
leaf may grow during the prefix; that growth is charged to its actual steps. -/
theorem finished_execution_after_prefix {B : ℕ}
    (count : ℕ) (hcount : count ≤ workStacks es)
    (hB : 0 < B) (P : List (SubexpFlatCount.Code B))
    (phase : MainCmd er es) (prefixSteps : ℕ) (start a : MainState er es)
    (storage : StorageReady count start) (hprefix : Eval phase prefixSteps start a)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width (SubexpFlatCount.flatPolynomial P)) :
    ∃ (steps : ℕ) (finalRegs : Fin 8 → Bool),
      steps ≤ 5 * prefixSteps +
        3 * SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial P) +
        2 * (start.stacks (persistent es 9)).length + 2 * (modulus.length + B) +
        3 * count + workRegs er + 13 ∧
      Eval (.seq phase (.seq (procedure er es count hcount).invoke (finishLeaf er es)))
        steps start
        (finishedData (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P))) ∧
      StorageReady count
        (finishedData (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P))) ∧
      (finishedData (result count hcount a finalRegs modulus width
        (SubexpFlatCount.firstWord P))).regs (controlRegister er 2) =
          SubexpDecodeProgram.answer modulus (SubexpFlatCount.firstWord P) := by
  have hbits := selectedBits_after_eval count hcount hprefix
  rw [selectedBits_eq_zero count hcount start storage] at hbits
  have hleaf := BitProgram.trace_listStackBits _ [persistent es 9] (by simp)
    (compiled_trace hprefix (persistent es 0) (persistent es 0))
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at hleaf
  change (a.stacks (persistent es 9)).length ≤
    (start.stacks (persistent es 9)).length + prefixSteps at hleaf
  obtain ⟨n, finalRegs, hn, he, _⟩ :=
    execution_selected count hcount hB P a regs modulus width hwidth ready
  have hf := finishCost_result_le count hcount P a finalRegs modulus width
  refine ⟨prefixSteps + (n +
    finishCost (result count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P))),
    finalRegs, by omega, .seq hprefix (.seq he (finishLeaf_eval _)), ?_, ?_⟩
  · exact finished_ready count hcount a finalRegs modulus width _
  · exact finished_found count hcount a finalRegs modulus width _

/-- The real epilogue returns exactly the reader's next-iteration state,
with its original unread stream and an empty parser payload. -/
theorem finished_callback_state (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool)
    (hp : a.stacks (persistent es 8) = []) :
    finishedData (result count hcount a regs modulus width word) =
      RecordPrograms.state (ports er es) (finishedData (result count hcount a regs modulus width word))
        false true (SubexpDecodeProgram.answer modulus word) (a.stacks (persistent es 7)) [] := by
  apply finished_record_state
  · exact result_persistent_frame count hcount a regs modulus width word 7
      (by decide) (by decide) (by decide)
  · exact (result_persistent_frame count hcount a regs modulus width word 8
      (by decide) (by decide) (by decide)).trans hp
  · exact result_answer count hcount a regs modulus width word

/-- A subsequent parser callback and physical transfer start the next layout
with empty ordinary storage and the new leaf in forward order. -/
theorem next_leaf_ready (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word tail bits : List Bool) :
    let next := transferredData
      (leafInput (finishedData (result count hcount a regs modulus width word)) tail bits)
    StorageReady count next ∧
      next.stacks (persistent es 9) = bits ∧
      next.stacks (persistent es 8) = [] ∧
      next.stacks (persistent es 7) = tail := by
  dsimp only
  refine ⟨transferred_ready count hcount _
    (leafInput_ready count hcount _ tail bits
      (finished_ready count hcount a regs modulus width word)), ?_⟩
  exact transfer_leafInput _ tail bits (finished_reusable count hcount a regs modulus width word).1

end SubexponentialSAT.SubexpMainReady

end OAI.Algorithms
