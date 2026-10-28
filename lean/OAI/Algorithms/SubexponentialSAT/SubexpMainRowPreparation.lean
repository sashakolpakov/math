import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowPreclear
import OAI.Algorithms.SubexponentialSAT.SubexpMainRowSetup
import OAI.Algorithms.SubexponentialSAT.SubexpDenseRowTableExecution

namespace OAI.Algorithms

/-! Complete physical preparation for the row traversal. The preclear,
source-context constructor, and six preserving input copies are all actual
fixed programs. The resulting workspace conditions are conclusions. -/

namespace SubexponentialSAT.SubexpMainRowPreparation

open BitProgram StructuredCalls SubexpMainProgram
open SubexpLayoutPorts (Allocation ordinary master)

attribute [local simp] Fin.coe_ofNat_eq_mod

noncomputable def pre {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  SubexpMainRowPreclear.result alloc a

def procedure (er : ℕ) {es : ℕ} (alloc : Allocation es) : Procedure er es :=
  SubexpProcedureCompose.sequence (SubexpMainRowPreclear.procedure er alloc)
    (SubexpMainRowSetup.procedure er alloc)

noncomputable def result {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :=
  SubexpMainRowSetup.result alloc (pre alloc a)

noncomputable def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  SubexpMainRowPreclear.runtimeBound alloc a +
    SubexpMainRowSetup.runtimeBound alloc (pre alloc a) + 1

theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    ∃ n ≤ runtimeBound alloc a, Eval (procedure er alloc).invoke n a (result alloc a) := by
  have hc := SubexpMainRowPreclear.execution alloc a
  obtain ⟨n, hn, hs⟩ := SubexpMainRowSetup.execution alloc (pre alloc a)
  exact ⟨SubexpMainRowPreclear.runtimeBound alloc a + n + 1,
    by unfold runtimeBound; omega, SubexpProcedureCompose.sequence_invoke _ _ hc hs⟩

theorem result_native {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 256) (hi : i.val < 250) :
    (result alloc a).stacks (ordinary alloc ⟨i.val, by omega⟩) =
      (SubexpSourceRowContext.result (SubexpMainRowSetup.projected alloc (pre alloc a))).stacks i :=
  SubexpMainRowSetup.result_native alloc (pre alloc a) i hi

theorem result_header {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 6) :
    (result alloc a).stacks (SubexpMainRowHeader.targetPort alloc i) =
      a.stacks (SubexpMainRowHeader.sourcePort alloc i) := by
  rw [result, SubexpMainRowSetup.result_header]
  fin_cases i <;> exact SubexpMainRowPreclear.result_master alloc a _

/-- The universal source generator's whole scratch bank is genuinely empty. -/
theorem result_workspace {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 49) :
    (result alloc a).stacks (ordinary alloc
      ⟨(Subexp.UniversalRowWorkspace.port i).val, by
        have := Subexp.UniversalRowWorkspace.port_lt_cache i; omega⟩) = [] := by
  let j : Fin 256 := ⟨(Subexp.UniversalRowWorkspace.port i).val,
    lt_trans (Subexp.UniversalRowWorkspace.port_lt_cache i) (by decide)⟩
  have hj : j.val < 250 := lt_trans (Subexp.UniversalRowWorkspace.port_lt_cache i) (by decide)
  rw [result_native alloc a j hj]
  have hn : ¬ SubexpSourceRowContext.NeedsClear j := by
    simp only [SubexpSourceRowContext.NeedsClear, Fin.ext_iff,
      Fin.coe_ofNat_eq_mod, j, Subexp.UniversalRowWorkspace.port_val]
    split_ifs <;> omega
  let d : SubexpSourceRowContext.Data := SubexpMainRowSetup.projected alloc (pre alloc a)
  change (SubexpSourceRowContext.result d).stacks j = []
  rw [SubexpSourceRowContext.result_frame d j hn]
  have hmap : (SubexpMainRowSetup.contextProcedure er alloc).stack j =
      ordinary alloc ⟨j.val, by omega⟩ := by
    change SubexpSourceRowContext.Main.stackMap (SubexpMainRowSetup.contextAllocation alloc) j = _
    have h250 : j ≠ SubexpSourceRowContext.radiusInput := by
      intro he; have he' := congrArg (fun k : Fin 256 => k.val) he
      change j.val = 250 at he'; omega
    have h251 : j ≠ SubexpSourceRowContext.targetWidthInput := by
      intro he; have he' := congrArg (fun k : Fin 256 => k.val) he
      change j.val = 251 at he'; omega
    simp only [SubexpSourceRowContext.Main.stackMap, ite_eq_right h250, ite_eq_right h251, ordinary]
  change (pre alloc a).stacks ((SubexpMainRowSetup.contextProcedure er alloc).stack j) = []
  rw [hmap]
  exact SubexpMainRowPreclear.result_workspace alloc a i

theorem result_high_empty {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 288) (hi : i.val = 255 ∨ 257 ≤ i.val ∧ i.val ≤ 263 ∨ 266 ≤ i.val) :
    (result alloc a).stacks (ordinary alloc ⟨i.val, by omega⟩) = [] := by
  let q := ordinary alloc ⟨i.val, by omega⟩
  have hq : q.val = i.val := rfl
  have ht (j : Fin 6) : SubexpMainRowHeader.targetPort alloc j ≠ q := by
    intro he
    have hv := congrArg (fun k : Fin (totalStacks es) => k.val) he
    fin_cases j <;>
      norm_num [SubexpMainRowHeader.targetPort, ordinary, q] at hv <;> omega
  have htmp : ordinary alloc 319 ≠ q := by
    intro he
    have hv := congrArg (fun k : Fin (totalStacks es) => k.val) he
    change 319 = i.val at hv
    omega
  have hb := alloc.enough.trans alloc.within
  change (SubexpMainRowHeader.installed alloc
    (SubexpMainRowSetup.contextResult alloc (pre alloc a))).stacks q = []
  rw [SubexpMainRowHeader.installed_frame alloc _ q ht htmp,
    SubexpMainRowSetup.context_high_frame alloc _ q (by rw [hq]; omega)
      (by rw [hq]; omega)]
  apply SubexpMainRowPreclear.result_cleared
  change SubexpMainRowPreclear.Selected i.val
  dsimp [SubexpMainRowPreclear.Selected]
  omega

theorem result_zero87 {er es : ℕ} (alloc : Allocation es) (a : MainState er es) :
    (result alloc a).stacks (ordinary alloc 87) = [] := by
  let i : Fin 256 := ⟨87, by decide⟩
  have hp : ordinary alloc (87 : Fin 672) = ordinary alloc ⟨i.val, by omega⟩ := by
    apply congrArg (ordinary alloc)
    apply Fin.ext
    rfl
  rw [hp]
  exact (result_native alloc a i (by decide)).trans
    (SubexpSourceRowContext.result_empty _ i (by decide)
      (SubexpSourceRowContext.copies_avoid i (by decide)) (by decide) (by decide) (by decide))

def store {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : Fin 288 → List Bool :=
  fun i => a.stacks (ordinary alloc ⟨i.val, by omega⟩)

/-- The real preparation discharges every scratch premise of the complete
row traversal. The two hypotheses identify its retained input masters. -/
theorem table_ready {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (D : ℕ) (scopes : List (List ℕ)) (regs : Fin 25 → Bool)
    (hs : a.stacks (master alloc 0) = SubexpDenseRowTableProgram.scopesCode scopes)
    (hd : a.stacks (master alloc 8) = List.replicate D true) :
    SubexpDenseRowTableProgram.TableReady ⟨regs, store alloc (result alloc a)⟩ D scopes := by
  refine ⟨(result_header alloc a 0).trans hs, (result_header alloc a 1).trans hd, ?_⟩
  intro i hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  · exact result_zero87 alloc a
  all_goals exact result_high_empty alloc a _ (by decide)

theorem high_clean {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (i : Fin 288) (hi : 270 ≤ i.val) :
    store alloc (result alloc a) i = [] :=
  result_high_empty alloc a i (by omega)

end SubexponentialSAT.SubexpMainRowPreparation

end OAI.Algorithms
