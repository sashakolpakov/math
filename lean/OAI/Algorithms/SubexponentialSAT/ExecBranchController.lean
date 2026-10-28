import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ExecBranchControllerSupport
import OAI.Algorithms.SubexponentialSAT.ExecPetalChildProgram
import OAI.Algorithms.SubexponentialSAT.RegisterResetProgram

namespace OAI.Algorithms

/-!
# Concrete two-child controller

The pending list and accumulated leaves are preserved verbatim. The parent,
core, and selected family are copied for each of the two concrete child
programs. Both results are framed as worklist records. All retained inputs,
the child workspace, and all Boolean registers are cleared before return.
-/

namespace SubexponentialSAT.ExecBranchController

open BitProgram StructuredCalls ExecBranchControllerSupport


abbrev formulaCode := ExecCoreChildProgram.formulaCode
abbrev clauseCode := ExecCoreChildProgram.clauseCode
abbrev volume := ExecCoreChildProgram.inputVolume

def inputFront (pending leaves : List Bool) (F selected : List (List ℕ)) (H : List ℕ) : Front :=
  ![pending, leaves, [], [], formulaCode F, clauseCode H, formulaCode selected]

def outputFront (pending leaves childA childB : List Bool) : Front :=
  ![pending, leaves, ExecWorklistProgram.record childA, ExecWorklistProgram.record childB, [], [], []]

def inputState (regs : Regs) (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) : Data :=
  idle regs (inputFront pending leaves F selected H)

def outputState (pending leaves : List Bool) (F selected : List (List ℕ)) (H : List ℕ) : Data :=
  idle (fun _ => false) (outputFront pending leaves
    (formulaCode (ExecCoreChildProgram.result F selected H))
    (formulaCode (ExecPetalChildProgram.result F selected H)))

@[simp] theorem outputState_pending (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) :
    (outputState pending leaves F selected H).stacks 0 = pending := rfl

@[simp] theorem outputState_leaves (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) :
    (outputState pending leaves F selected H).stacks 1 = leaves := rfl

@[simp] theorem outputState_childA (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) :
    (outputState pending leaves F selected H).stacks 2 =
      ExecWorklistProgram.record (formulaCode (ExecCoreChildProgram.result F selected H)) := rfl

@[simp] theorem outputState_childB (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) :
    (outputState pending leaves F selected H).stacks 3 =
      ExecWorklistProgram.record (formulaCode (ExecPetalChildProgram.result F selected H)) := rfl

@[simp] theorem outputState_regs (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) (i : Fin 15) :
    (outputState pending leaves F selected H).regs i = false := rfl

theorem outputState_clean (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) (i : Fin 23) (hi : 4 ≤ i.val) :
    (outputState pending leaves F selected H).stacks i = [] := by
  let front := outputFront pending leaves
    (formulaCode (ExecCoreChildProgram.result F selected H))
    (formulaCode (ExecPetalChildProgram.result F selected H))
  revert hi
  refine Fin.addCases (m := 7) (n := 16) (fun j => ?_) (fun j => ?_) i
  · intro hj
    change (idle (fun _ => false) front).stacks (frontPort j) = []
    simp only [idle, state_front]
    fin_cases j
    · change 4 ≤ 0 at hj
      omega
    · change 4 ≤ 1 at hj
      omega
    · change 4 ≤ 2 at hj
      omega
    · change 4 ≤ 3 at hj
      omega
    · rfl
    · rfl
    · rfl
  · intro _
    change (idle (fun _ => false) front).stacks (bankPort j) = []
    simp only [idle, state_bank, emptyBank]

def Ready (d : Data) : Prop :=
  d.stacks 2 = [] ∧ d.stacks 3 = [] ∧ ∀ i : Fin 16, d.stacks (bankPort i) = []

theorem input_eq (d : Data) (F selected : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 4 = formulaCode F) (hH : d.stacks 5 = clauseCode H)
    (hS : d.stacks 6 = formulaCode selected) (hr : Ready d) :
    d = inputState d.regs (d.stacks 0) (d.stacks 1) F selected H := by
  apply congrArg₂ StructuredProgram.State.mk rfl
  funext i
  refine Fin.addCases (m := 7) (n := 16) (fun j => ?_) (fun j => ?_) i
  · change d.stacks (frontPort j) =
      (idle d.regs (inputFront (d.stacks 0) (d.stacks 1) F selected H)).stacks (frontPort j)
    simp only [idle, state_front]
    fin_cases j
    · rfl
    · rfl
    · exact hr.1
    · exact hr.2.1
    · exact hF
    · exact hH
    · exact hS
  · change d.stacks (bankPort j) =
      (idle d.regs (inputFront (d.stacks 0) (d.stacks 1) F selected H)).stacks (bankPort j)
    simpa only [idle, state_bank, emptyBank] using hr.2.2 j

theorem loaded_ready (regs : Regs) (front : Front) :
    ExecCoreChildProgram.InputReady (loaded regs front) := by
  intro i h9 h12 h13
  fin_cases i <;>
    first
    | exact False.elim (h9 rfl)
    | exact False.elim (h12 rfl)
    | exact False.elim (h13 rfl)
    | rfl

abbrev command : Cmd 15 23 :=
  .seq (buildChild ExecCoreChildProgram.program 0)
    (.seq (buildChild ExecPetalChildProgram.program 1)
      (.seq cleanInputs RegisterResetProgram.all))

theorem command_eval (regs : Regs) (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) :
    ∃ n ≤ 24000 * (volume F selected H) ^ 2,
      Eval command n (inputState regs pending leaves F selected H)
        (outputState pending leaves F selected H) := by
  let f0 := inputFront pending leaves F selected H
  let wordA := formulaCode (ExecCoreChildProgram.result F selected H)
  let wordB := formulaCode (ExecPetalChildProgram.result F selected H)
  obtain ⟨a, haReady, haOut, n, hn, ha⟩ :=
    ExecCoreChildProgram.program_runsIn F selected H (loaded (reset regs) f0) rfl rfl rfl
      (loaded_ready (reset regs) f0)
  have haEq : a = ExecClauseFiltersProgram.state a.regs [] [] [] wordA [] [] := by
    simpa only [haOut] using ExecClauseFiltersProgram.ready_eq_state a haReady
  rw [haEq] at ha
  have hA := buildChild_eval ExecCoreChildProgram.program 0 regs f0 wordA a.regs ha
  simp only [show outputPort 0 = 2 from rfl, show f0 2 = [] from rfl, List.append_nil] at hA
  let ra := emittedRegs (reset a.regs)
  let fa : Front := Function.update f0 2 (ExecWorklistProgram.record wordA)
  obtain ⟨b, hbReady, hbOut, m, hm, hb⟩ :=
    ExecPetalChildProgram.program_runsIn F selected H (loaded (reset ra) fa) rfl rfl rfl
      (loaded_ready (reset ra) fa)
  have hbEq : b = ExecClauseFiltersProgram.state b.regs [] [] [] wordB [] [] := by
    simpa only [hbOut] using ExecClauseFiltersProgram.ready_eq_state b hbReady
  rw [hbEq] at hb
  have hB := buildChild_eval ExecPetalChildProgram.program 1 ra fa wordB b.regs hb
  simp only [show outputPort 1 = 3 from rfl, show fa 3 = [] from rfl, List.append_nil] at hB
  let rb := emittedRegs (reset b.regs)
  let fb : Front := Function.update fa 3 (ExecWorklistProgram.record wordB)
  have hclean := cleanInputs_eval rb fb
  have hreset := RegisterResetProgram.all_eval (idle (reset rb) (cleanFront fb))
  have hfinal : cleanFront fb = outputFront pending leaves wordA wordB := by
    funext i
    fin_cases i <;> simp [cleanFront, fb, fa, f0, inputFront, outputFront]
  have hfull := hA.seq (hB.seq (hclean.seq hreset))
  rw [hfinal] at hfull
  change Eval command _ (inputState regs pending leaves F selected H)
    (outputState pending leaves F selected H) at hfull
  refine ⟨_, ?_, hfull⟩
  let V := volume F selected H
  have hv : 1 ≤ V := by dsimp [V, volume, ExecCoreChildProgram.inputVolume]; omega
  have hsq : V ≤ V ^ 2 := by nlinarith [Nat.mul_le_mul_left V hv]
  have hsum : (formulaCode F).length + (clauseCode H).length +
      (formulaCode selected).length ≤ V := by
    change (formulaCode F).length + (clauseCode H).length +
      (formulaCode selected).length ≤ (formulaCode selected).length +
      (formulaCode F).length + 2 * (clauseCode H).length + 3
    omega
  have hlenA : wordA.length ≤ V := by
    have h := ExecCoreChildProgram.result_length_le F selected H
    change wordA.length ≤ (formulaCode F).length + 2 * (clauseCode H).length + 2 at h
    change wordA.length ≤ (formulaCode selected).length +
      (formulaCode F).length + 2 * (clauseCode H).length + 3
    omega
  have hlenB : wordB.length ≤ V := by
    have h := ExecPetalChildProgram.result_length_le F selected H
    change wordB.length + 1 ≤ V at h
    omega
  have hload0 : loadCost f0 ≤ 7 * V + 15 := by
    change 7 * ((formulaCode F).length + (clauseCode H).length +
      (formulaCode selected).length) + 15 ≤ _
    omega
  have hloadA : loadCost fa = loadCost f0 := by
    simp [loadCost, fa]
  have hcleanup : 2 * ((fb 4).length + (fb 5).length + (fb 6).length) + 9 ≤ 2 * V + 9 := by
    change 2 * ((formulaCode F).length + (clauseCode H).length +
      (formulaCode selected).length) + 9 ≤ _
    omega
  change n ≤ 3300 * V ^ 2 at hn
  change m ≤ 20000 * V ^ 2 at hm
  change loadCost f0 + (n + (8 * wordA.length + 10)) +
    (loadCost fa + (m + (8 * wordB.length + 10)) +
      (2 * ((fb 4).length + (fb 5).length + (fb 6).length) + 9 + 15)) ≤ 24000 * V ^ 2
  rw [hloadA]
  nlinarith

def program := compiled command 4 2

theorem program_runsIn (regs : Regs) (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) :
    RunsIn program (25000 * (volume F selected H) ^ 2)
      ((inputState regs pending leaves F selected H).withPC (some program.entry))
      ((outputState pending leaves F selected H).withPC none) := by
  obtain ⟨n, hn, ht⟩ := command_eval regs pending leaves F selected H
  refine ⟨n + 1, ?_, compiled_halt_trace ht 4 2⟩
  have hv : 0 < volume F selected H := by unfold volume ExecCoreChildProgram.inputVolume; omega
  have hp := pow_pos hv 2
  omega

theorem program_runsIn_from_state (d : Data) (F selected : List (List ℕ)) (H : List ℕ)
    (hF : d.stacks 4 = formulaCode F) (hH : d.stacks 5 = clauseCode H)
    (hS : d.stacks 6 = formulaCode selected) (hr : Ready d) :
    RunsIn program (25000 * (volume F selected H) ^ 2)
      (d.withPC (some program.entry))
      ((outputState (d.stacks 0) (d.stacks 1) F selected H).withPC none) := by
  have h := program_runsIn d.regs (d.stacks 0) (d.stacks 1) F selected H
  simpa only [← input_eq d F selected H hF hH hS hr] using h

/-- Simulation of the three-input source interface. The child words remain
source-stack data for the enclosing worklist program; this does not assert
that a halted primitive machine returns arbitrary binary words. -/
theorem primitive_execution (regs : Regs) (pending leaves : List Bool)
    (F selected : List (List ℕ)) (H : List ℕ) :
    Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (25000 * (volume F selected H) ^ 2))
      (primitiveCfg program ((inputState regs pending leaves F selected H).withPC (some program.entry)))
      (primitiveCfg program ((outputState pending leaves F selected H).withPC none)) :=
  BitProgram.primitive_execution program (program_runsIn regs pending leaves F selected H)

end SubexponentialSAT.ExecBranchController

end OAI.Algorithms
