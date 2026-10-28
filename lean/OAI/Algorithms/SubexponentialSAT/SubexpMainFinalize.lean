import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainDecode
import OAI.Algorithms.SubexponentialSAT.SubexpProcedureCompose
import OAI.Algorithms.SubexponentialSAT.WorkspaceCleanupProgram
import OAI.Algorithms.SubexponentialSAT.BitProgramSelectedSpace

namespace OAI.Algorithms

/-!
# Actual decoding followed by reusable-workspace cleanup

The ordinary workspace is cleared by a real fixed program after the decoded
answer has been written to persistent storage. Threshold words and other
persistent data survive. The time bound follows from actual stack-bit growth,
so restoration of the next leaf's workspace is not a free logical operation.
-/

namespace SubexponentialSAT.SubexpMainFinalize

open StructuredCalls SubexpMainProgram

namespace Cleanup

def procedure := WorkspaceCleanupProgram.Main.procedure
abbrev bound {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) : ℕ := WorkspaceCleanupProgram.Main.bound count hcount a
noncomputable abbrev result {er es : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) : MainState er es := WorkspaceCleanupProgram.Main.result count hcount a

end Cleanup

variable {er es : ℕ}

def withCleanup (decoder : Procedure er es) (count : ℕ)
    (hcount : count ≤ workStacks es) : Procedure er es :=
  SubexpProcedureCompose.sequence decoder (Cleanup.procedure er es count hcount)

theorem withCleanup_execution (decoder : Procedure er es) (count : ℕ)
    (hcount : count ≤ workStacks es) {n : ℕ} {a b : MainState er es}
    (h : Eval decoder.invoke n a b) :
    Eval (withCleanup decoder count hcount).invoke
      (n + Cleanup.bound count hcount b + 1) a (Cleanup.result count hcount b) :=
  SubexpProcedureCompose.sequence_invoke _ _ h
    (WorkspaceCleanupProgram.Main.execution count hcount b)

/-- Every bit in the cleanup region was present on entry or was allocated by
an actual source instruction. Cleanup therefore has linear additional cost. -/
theorem withCleanup_bound (decoder : Procedure er es) (count : ℕ)
    (hcount : count ≤ workStacks es) {n : ℕ} {a b : MainState er es}
    (h : Eval decoder.invoke n a b) :
    n + Cleanup.bound count hcount b + 1 ≤
      3 * n + 2 * BitProgram.stackBits a.stacks + 3 * count + 2 := by
  let p := ProgramLinking.liftProgram decoder.program decoder.registerMap decoder.stack
  have ht : BitProgram.Trace p n (a.withPC (some p.entry)) (b.withPC none) := by
    change Eval (.call p) n a b at h
    cases h with
    | call _ ht => exact ht
  have hc := WorkspaceCleanupProgram.Main.bound_after_runsIn count hcount p
    (show BitProgram.RunsIn p n (a.withPC (some p.entry)) (b.withPC none) from
      ⟨n, le_rfl, ht⟩)
  change n + WorkspaceCleanupProgram.Main.bound count hcount b + 1 ≤ _
  omega

/-- Only the selected workspace is charged. In particular the bound is
independent of the arbitrary unread leaf stream on a persistent stack. -/
theorem withCleanup_selected_bound (decoder : Procedure er es) (count : ℕ)
    (hcount : count ≤ workStacks es) {n : ℕ} {a b : MainState er es}
    (h : Eval decoder.invoke n a b) :
    n + Cleanup.bound count hcount b + 1 ≤
      3 * n + 2 * WorkspaceCleanupProgram.Main.selectedBits count hcount a +
        3 * count + 2 := by
  let p := ProgramLinking.liftProgram decoder.program decoder.registerMap decoder.stack
  have ht : BitProgram.Trace p n (a.withPC (some p.entry)) (b.withPC none) := by
    change Eval (.call p) n a b at h
    cases h with
    | call _ ht => exact ht
  have hs := BitProgram.trace_listStackBits p
    (WorkspaceCleanupProgram.Main.selectedPorts es count hcount)
    (WorkspaceCleanupProgram.prefixPorts_nodup _ _) ht
  change WorkspaceCleanupProgram.Main.selectedBits count hcount b ≤
    WorkspaceCleanupProgram.Main.selectedBits count hcount a + n at hs
  change n + (2 * WorkspaceCleanupProgram.Main.selectedBits count hcount b +
    3 * count + 1) + 1 ≤ _
  omega

def procedure (er es count : ℕ) (hcount : count ≤ workStacks es) : Procedure er es :=
  withCleanup (SubexpMainDecode.procedure er es) count hcount

noncomputable def finalData (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool) :
    MainState er es :=
  Cleanup.result count hcount
    ((SubexpMainDecode.procedure er es).install a
      (SubexpMainDecode.localResult regs modulus width word))

/-- The decoder uses only low scratch ports below eight and its three
persistent ports. In particular it cannot touch a protected threshold bank. -/
theorem decoder_workspace_frame (a : MainState er es)
    (result : StructuredProgram.State 8 8) (i : Fin (totalStacks es))
    (h8 : 8 ≤ i.val) (hwork : i.val < workStacks es) :
    ((SubexpMainDecode.procedure er es).install a result).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  change SubexpMainDecode.stackMap es j = i at hj
  have hv := congrArg Fin.val hj
  have hm : (SubexpMainDecode.stackMap es j).val < 8 ∨
      workStacks es ≤ (SubexpMainDecode.stackMap es j).val := by
    fin_cases j
    · right
      change workStacks es ≤ (persistent es 10).val
      simp [persistent]
    · left
      change (SubexpMainDecode.scratch es 1).val < 8
      simp [SubexpMainDecode.scratch]
    · left
      change (SubexpMainDecode.scratch es 2).val < 8
      simp [SubexpMainDecode.scratch]
    · left
      change (SubexpMainDecode.scratch es 3).val < 8
      simp [SubexpMainDecode.scratch]
    · left
      change (SubexpMainDecode.scratch es 4).val < 8
      simp [SubexpMainDecode.scratch]
    · right
      change workStacks es ≤ (persistent es 12).val
      simp [persistent]
    · left
      change (SubexpMainDecode.scratch es 6).val < 8
      simp [SubexpMainDecode.scratch]
    · right
      change workStacks es ≤ (persistent es 13).val
      simp [persistent]
  omega

theorem finalData_workspace_frame (count : ℕ) (hcount : count ≤ workStacks es)
    (a : MainState er es) (regs : Fin 8 → Bool) (modulus width word : List Bool)
    (i : Fin (totalStacks es)) (h8 : 8 ≤ i.val)
    (hi : count ≤ i.val) (hwork : i.val < workStacks es) :
    (finalData count hcount a regs modulus width word).stacks i = a.stacks i := by
  unfold finalData
  rw [WorkspaceCleanupProgram.Main.result_frame count hcount _ i hi]
  exact decoder_workspace_frame a _ i h8 hwork

/-- The finalizer preserves the real answer while physically restoring every
selected work stack. Count and all port locations are fixed before input. -/
theorem execution {B : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (hB : 0 < B) (P : List (SubexpFlatCount.Code B)) (a : MainState er es)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width (SubexpFlatCount.flatPolynomial P)) :
    ∃ (steps : ℕ) (finalRegs : Fin 8 → Bool),
      steps ≤ 3 * SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial P) +
        2 * BitProgram.stackBits a.stacks + 3 * count + 2 ∧
      Eval (procedure er es count hcount).invoke steps a
        (finalData count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) ∧
      ((finalData count hcount a finalRegs modulus width
        (SubexpFlatCount.firstWord P)).stacks (persistent es 10)).head? =
          some (SubexpDecodeProgram.answer modulus (SubexpFlatCount.firstWord P)) ∧
      (∀ i : Fin (totalStacks es), i.val < count →
        (finalData count hcount a finalRegs modulus width
          (SubexpFlatCount.firstWord P)).stacks i = []) ∧
      (∀ i : Fin 32, i ≠ 10 → i ≠ 12 → i ≠ 13 →
        (finalData count hcount a finalRegs modulus width
          (SubexpFlatCount.firstWord P)).stacks (persistent es i) =
            a.stacks (persistent es i)) := by
  obtain ⟨n, finalRegs, hn, hd⟩ :=
    SubexpMainDecode.execution hB P a regs modulus width hwidth ready
  let b := (SubexpMainDecode.procedure er es).install a
    (SubexpMainDecode.localResult finalRegs modulus width (SubexpFlatCount.firstWord P))
  refine ⟨n + Cleanup.bound count hcount b + 1, finalRegs, ?_, ?_, ?_, ?_, ?_⟩
  · have hb := withCleanup_bound (SubexpMainDecode.procedure er es) count hcount hd
    dsimp [b] at *
    omega
  · exact withCleanup_execution (SubexpMainDecode.procedure er es) count hcount hd
  · change ((Cleanup.result count hcount b).stacks (persistent es 10)).head? = _
    rw [WorkspaceCleanupProgram.Main.result_persistent]
    exact SubexpMainDecode.installed_head a finalRegs modulus width _
  · intro i hi
    exact WorkspaceCleanupProgram.Main.result_cleared count hcount b i hi
  · intro i h10 h12 h13
    change (Cleanup.result count hcount b).stacks (persistent es i) = _
    rw [WorkspaceCleanupProgram.Main.result_persistent]
    exact SubexpMainDecode.installed_frame a _ i h10 h12 h13

/-- The per-leaf form excludes persistent unread data from the cleanup cost. -/
theorem execution_selected {B : ℕ} (count : ℕ) (hcount : count ≤ workStacks es)
    (hB : 0 < B) (P : List (SubexpFlatCount.Code B)) (a : MainState er es)
    (regs : Fin 8 → Bool) (modulus width : List Bool) (hwidth : width.length = B)
    (ready : (SubexpMainDecode.procedure er es).project a =
      SubexpFlatCount.start regs modulus width (SubexpFlatCount.flatPolynomial P)) :
    ∃ (steps : ℕ) (finalRegs : Fin 8 → Bool),
      steps ≤ 3 * SubexpFlatCount.budget B modulus (SubexpFlatCount.flatPolynomial P) +
        2 * WorkspaceCleanupProgram.Main.selectedBits count hcount a + 3 * count + 2 ∧
      Eval (procedure er es count hcount).invoke steps a
        (finalData count hcount a finalRegs modulus width (SubexpFlatCount.firstWord P)) ∧
      ((finalData count hcount a finalRegs modulus width
        (SubexpFlatCount.firstWord P)).stacks (persistent es 10)).head? =
          some (SubexpDecodeProgram.answer modulus (SubexpFlatCount.firstWord P)) ∧
      (∀ i : Fin (totalStacks es), i.val < count →
        (finalData count hcount a finalRegs modulus width
          (SubexpFlatCount.firstWord P)).stacks i = []) ∧
      (∀ i : Fin 32, i ≠ 10 → i ≠ 12 → i ≠ 13 →
        (finalData count hcount a finalRegs modulus width
          (SubexpFlatCount.firstWord P)).stacks (persistent es i) =
            a.stacks (persistent es i)) := by
  obtain ⟨n, finalRegs, hn, hd⟩ :=
    SubexpMainDecode.execution hB P a regs modulus width hwidth ready
  let b := (SubexpMainDecode.procedure er es).install a
    (SubexpMainDecode.localResult finalRegs modulus width (SubexpFlatCount.firstWord P))
  refine ⟨n + Cleanup.bound count hcount b + 1, finalRegs, ?_, ?_, ?_, ?_, ?_⟩
  · have hb := withCleanup_selected_bound (SubexpMainDecode.procedure er es) count hcount hd
    dsimp [b] at *
    omega
  · exact withCleanup_execution (SubexpMainDecode.procedure er es) count hcount hd
  · change ((Cleanup.result count hcount b).stacks (persistent es 10)).head? = _
    rw [WorkspaceCleanupProgram.Main.result_persistent]
    exact SubexpMainDecode.installed_head a finalRegs modulus width _
  · intro i hi
    exact WorkspaceCleanupProgram.Main.result_cleared count hcount b i hi
  · intro i h10 h12 h13
    change (Cleanup.result count hcount b).stacks (persistent es i) = _
    rw [WorkspaceCleanupProgram.Main.result_persistent]
    exact SubexpMainDecode.installed_frame a _ i h10 h12 h13

end SubexponentialSAT.SubexpMainFinalize

end OAI.Algorithms
