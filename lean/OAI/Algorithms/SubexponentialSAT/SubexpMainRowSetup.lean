import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpSourceRowContextCalls
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowHeader
import OAI.Algorithms.SubexponentialSAT.SubexpProcedureCompose

namespace OAI.Algorithms

/-!
# Actual source-row context and traversal-input preparation

This fixed program first initializes the source-field arithmetic context,
then copies the retained scopes, packing metadata, dimension, and scalar
masters into the row traversal's private inputs. All saved layout masters
and the source cache survive. The traversal itself is a subsequent phase.
-/

namespace SubexponentialSAT.SubexpMainRowSetup

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)

attribute [local simp] Fin.coe_ofNat_eq_mod

def contextAllocation {es : ℕ} (alloc : Allocation es) :
    SubexpSourceRowContext.Main.Allocation es where
  ordinaryCount := alloc.ordinaryCount
  enough := by have := alloc.enough; omega
  within := alloc.within

def contextProcedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es where
  registers := 16
  stackCount := 256
  labels := size SubexpSourceRowContext.command + 1
  program := SubexpSourceRowContext.program
  register := ⟨fun i => i.castLE (by dsimp [workRegs]; omega), by
    intro i j h
    exact Fin.ext (congrArg (fun q : Fin (workRegs er) => q.val) h)⟩
  stack := SubexpSourceRowContext.Main.port (contextAllocation alloc)

def projected {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  (contextProcedure er alloc).project a

noncomputable def contextResult {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  SubexpSourceRowContext.Main.result er (contextAllocation alloc) a

theorem context_invocation {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    ∃ n ≤ SubexpSourceRowContext.runtimeBound (projected alloc a),
      Eval (contextProcedure er alloc).invoke n a (contextResult alloc a) := by
  obtain ⟨n, hn, ht⟩ := SubexpSourceRowContext.program_runs (projected alloc a)
  exact ⟨n, hn, Procedure.invoke_trace _ _ _ ht⟩

theorem context_native {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 256) (hi : i.val < 250) :
    (contextResult alloc a).stacks (ordinary alloc ⟨i.val, by omega⟩) =
      (SubexpSourceRowContext.result (projected alloc a)).stacks i := by
  have hm : (contextProcedure er alloc).stack i = ordinary alloc ⟨i.val, by omega⟩ := by
    have h250 : i ≠ SubexpSourceRowContext.radiusInput := by
      intro h; have hv := congrArg (fun j : Fin 256 => j.val) h
      change i.val = 250 at hv
      omega
    have h251 : i ≠ SubexpSourceRowContext.targetWidthInput := by
      intro h; have hv := congrArg (fun j : Fin 256 => j.val) h
      change i.val = 251 at hv
      omega
    change SubexpSourceRowContext.Main.stackMap (contextAllocation alloc) i =
      ordinary alloc ⟨i.val, by omega⟩
    simp only [SubexpSourceRowContext.Main.stackMap, ite_eq_right h250, ite_eq_right h251, ordinary]
  have h := embedState_stack (contextProcedure er alloc).registerMap
    (contextProcedure er alloc).stack a
    (SubexpSourceRowContext.result (projected alloc a))
    (contextProcedure er alloc).stack.injective i
  change (contextResult alloc a).stacks ((contextProcedure er alloc).stack i) =
    (SubexpSourceRowContext.result (projected alloc a)).stacks i at h
  rw [hm] at h
  exact h

theorem context_high_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hlo : 250 ≤ i.val) (hhi : i.val < workStacks es) :
    (contextResult alloc a).stacks i = a.stacks i := by
  apply SubexpSourceRowContext.resultAt_frame
  intro j hj
  have hv := congrArg (fun q : Fin (totalStacks es) => q.val) hj
  change (SubexpSourceRowContext.Main.stackMap (contextAllocation alloc) j).val = i.val at hv
  by_cases h250 : j = SubexpSourceRowContext.radiusInput
  · subst j
    change workStacks es + 25 = i.val at hv
    omega
  by_cases h251 : j = SubexpSourceRowContext.targetWidthInput
  · subst j
    change workStacks es + 13 = i.val at hv
    omega
  simp only [SubexpSourceRowContext.Main.stackMap, ite_eq_right h250, ite_eq_right h251] at hv
  have hjlo : 250 ≤ j.val := by omega
  simp only [SubexpSourceRowContext.NeedsClear]
  intro h
  rcases h with h | h | h | h | h | h | h | h | h
  all_goals omega

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (contextProcedure er alloc)
    (SubexpMainRowHeader.procedure er alloc)

noncomputable def result {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    MainState er es := SubexpMainRowHeader.installed alloc (contextResult alloc a)

theorem header_low_frame {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin (totalStacks es)) (hi : i.val < 252) :
    (SubexpMainRowHeader.installed alloc a).stacks i = a.stacks i := by
  apply SubexpMainRowHeader.installed_frame
  · intro j he
    have hl : 252 ≤ (SubexpMainRowHeader.targetPort alloc j).val := by
      fin_cases j <;> norm_num [SubexpMainRowHeader.targetPort, ordinary]
    rw [he] at hl
    omega
  · intro he
    have hv := congrArg (fun q : Fin (totalStacks es) => q.val) he
    change 319 = i.val at hv
    omega

/-- Exact initialized low store, sufficient for the existing source-row
readiness theorem. The aliases250/251 are intentionally excluded. -/
theorem result_native {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 256) (hi : i.val < 250) :
    (result alloc a).stacks (ordinary alloc ⟨i.val, by omega⟩) =
      (SubexpSourceRowContext.result (projected alloc a)).stacks i := by
  rw [result, header_low_frame alloc _ _ (by change i.val < 252; omega)]
  exact context_native alloc a i hi

theorem result_header {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 6) :
    (result alloc a).stacks (SubexpMainRowHeader.targetPort alloc i) =
      a.stacks (SubexpMainRowHeader.sourcePort alloc i) := by
  rw [result, SubexpMainRowHeader.installed_target]
  apply context_high_frame
  · fin_cases i <;> change 250 ≤ 640 + _ <;> omega
  · have h (j : Fin 32) : (master alloc j).val < workStacks es :=
      (SubexpLayoutPorts.master_below_cleanup alloc j).trans_le alloc.within
    fin_cases i <;> exact h _

theorem context_header_project {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    ((SubexpMainRowHeader.procedure er alloc).project (contextResult alloc a)).stacks =
      ((SubexpMainRowHeader.procedure er alloc).project a).stacks := by
  funext i
  apply context_high_frame
  · change 250 ≤ (SubexpMainRowHeader.stackMap alloc i).val
    fin_cases i
    · change 250 ≤ 640
      omega
    · change 250 ≤ 648
      omega
    · change 250 ≤ 653
      omega
    · change 250 ≤ 645
      omega
    · change 250 ≤ 646
      omega
    · change 250 ≤ 649
      omega
    · change 250 ≤ 256
      omega
    · change 250 ≤ 264
      omega
    · change 250 ≤ 265
      omega
    · change 250 ≤ 252
      omega
    · change 250 ≤ 253
      omega
    · change 250 ≤ 254
      omega
    · change 250 ≤ 319
      omega
  · have hb := alloc.enough.trans alloc.within
    change (SubexpMainRowHeader.stackMap alloc i).val < workStacks es
    fin_cases i
    · change 640 < workStacks es
      omega
    · change 648 < workStacks es
      omega
    · change 653 < workStacks es
      omega
    · change 645 < workStacks es
      omega
    · change 646 < workStacks es
      omega
    · change 649 < workStacks es
      omega
    · change 256 < workStacks es
      omega
    · change 264 < workStacks es
      omega
    · change 265 < workStacks es
      omega
    · change 252 < workStacks es
      omega
    · change 253 < workStacks es
      omega
    · change 254 < workStacks es
      omega
    · change 319 < workStacks es
      omega

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  SubexpSourceRowContext.runtimeBound (projected alloc a) +
    SubexpMainRowHeader.runtimeBound alloc a + 1

theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    ∃ n ≤ runtimeBound alloc a, Eval (procedure er alloc).invoke n a (result alloc a) := by
  obtain ⟨nc, hnc, hec⟩ := context_invocation alloc a
  obtain ⟨nh, hnh, heh⟩ := SubexpMainRowHeader.execution alloc (contextResult alloc a)
  have hb : SubexpMainRowHeader.runtimeBound alloc (contextResult alloc a) =
      SubexpMainRowHeader.runtimeBound alloc a := by
    unfold SubexpMainRowHeader.runtimeBound
    rw [context_header_project]
  rw [hb] at hnh
  exact ⟨nc + nh + 1, by unfold runtimeBound; omega,
    SubexpProcedureCompose.sequence_invoke _ _ hec heh⟩

end SubexponentialSAT.SubexpMainRowSetup

end OAI.Algorithms
