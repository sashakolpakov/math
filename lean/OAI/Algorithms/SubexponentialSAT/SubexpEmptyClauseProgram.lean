import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpScopeMembershipProgram
import OAI.Algorithms.SubexponentialSAT.ExecSparsifyEncoding

namespace OAI.Algorithms

/-!
# A preserving empty-clause test on the actual encoded leaf

The fixed program searches for the one-bit encoding of an empty clause.
The leaf on stack 9 and every other caller word are preserved.  Only the
five empty membership work ports and one empty copy port are used.
-/

namespace SubexponentialSAT.SubexpEmptyClauseProgram

open BitProgram StructuredCalls

abbrev Data := StructuredProgram.State 10 10

def Ready (d : Data) : Prop :=
  (∀ i : Fin 10, i.val < 5 → d.stacks i = []) ∧ d.stacks 8 = []

abbrev atom (a : StructuredProgram.Atom 10 10) : Cmd 10 10 := .base (.atom a)

def copied (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks 0 (d.stacks 9)⟩

abbrev copyLeaf : Cmd 10 10 := .call (StackRoutines.copyProgram 9 0 8 0 1)

theorem copyLeaf_eval (d : Data) (h : Ready d) :
    Eval copyLeaf (7 * (d.stacks 9).length + 5) d (copied d) := by
  have ht := ListRegisterProgram.copy_run (9 : Fin 10) 0 8 (0 : Fin 10) 1
    (by decide) (by decide) (by decide) (by decide) d.regs d.stacks h.2
  apply Eval.call
  simpa [copied, ListRegisterProgram.Run, StackRoutines.copyStacks, h.1 0 (by decide)] using ht

abbrev loadQuery : Cmd 10 10 := .seq (atom (.set 0 false)) (atom (.push 2 0))

def queryLoaded (d : Data) : Data :=
  ⟨Function.update d.regs 0 false, Function.update d.stacks 2 (false :: d.stacks 2)⟩

theorem loadQuery_eval (d : Data) : Eval loadQuery 2 d (queryLoaded d) := by
  exact .seq (.base (.atom _ _)) (.base (.atom _ _))

abbrev clear (i : Fin 10) : Cmd 10 10 := .call (StackRoutines.clearProgram i 0 1)

def cleared (i : Fin 10) (d : Data) : Data :=
  ⟨readRegs d.regs 0 1 none, Function.update d.stacks i []⟩

theorem clear_eval (i : Fin 10) (d : Data) :
    Eval (clear i) (2 * (d.stacks i).length + 3) d (cleared i d) :=
  .call _ (ListRegisterProgram.clear_run i 0 1 d.regs d.stacks)

abbrev resetWork : Cmd 10 10 :=
  .seq (atom (.copy 0 4))
    (.seq (atom (.set 1 false))
      (.seq (atom (.set 2 false))
        (.seq (atom (.set 3 false))
          (.seq (atom (.set 4 false))
            (.seq (atom (.set 5 false)) (atom (.set 6 false)))))))

def resetResult (d : Data) : Data :=
  ⟨fun i => if i = 0 then d.regs 4 else if i.val < 7 then false else d.regs i,
    d.stacks⟩

theorem resetWork_eval (d : Data) : Eval resetWork 7 d (resetResult d) := by
  let d0 := (StructuredProgram.Atom.copy 0 4).eval d
  let d1 := (StructuredProgram.Atom.set 1 false).eval d0
  let d2 := (StructuredProgram.Atom.set 2 false).eval d1
  let d3 := (StructuredProgram.Atom.set 3 false).eval d2
  let d4 := (StructuredProgram.Atom.set 4 false).eval d3
  let d5 := (StructuredProgram.Atom.set 5 false).eval d4
  let d6 := (StructuredProgram.Atom.set 6 false).eval d5
  have he : Eval resetWork 7 d d6 :=
    .seq (.base (.atom _ _)) (.seq (.base (.atom _ _))
      (.seq (.base (.atom _ _)) (.seq (.base (.atom _ _))
        (.seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))))))
  have hd : d6 = resetResult d := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> rfl
    · rfl
  exact hd ▸ he

abbrev command : Cmd 10 10 :=
  .seq copyLeaf (.seq loadQuery (.seq SubexpScopeMembershipProgram.member
    (.seq (clear 0) (.seq (clear 1) (.seq (clear 2) resetWork)))))

def result (d : Data) (answer : Bool) : Data :=
  ⟨fun i => if i = 0 then answer else if i.val < 7 then false else d.regs i,
    d.stacks⟩

/-- A real membership search, including the preserving copy and all cleanup.
No clause-order, width, or nonempty-clause premise is needed. -/
theorem command_eval (records : List (List Bool)) (d : Data)
    (hbody : d.stacks 9 = Encoding.encodeList id records) (hr : Ready d) :
    ∃ t, t ≤ 100 * ((d.stacks 9).length + 1) ∧
      Eval command t d (result d (decide ([false] ∈ records))) := by
  let start := queryLoaded (copied d)
  have h0 : start.stacks 0 = Encoding.encodeList id records := by
    simp [start, queryLoaded, copied, hbody]
  have h1 : start.stacks 1 = [] := by
    simpa [start, queryLoaded, copied] using hr.1 1 (by decide)
  have h2 : start.stacks 2 = ([false] : List Bool).reverse := by
    simp [start, queryLoaded, copied, hr.1 2 (by decide)]
  have h3 : start.stacks 3 = [] := by
    simpa [start, queryLoaded, copied] using hr.1 3 (by decide)
  have h4 : start.stacks 4 = [] := by
    simpa [start, queryLoaded, copied] using hr.1 4 (by decide)
  obtain ⟨t, e, he, ht, hf, hlen, hout, hquery, hcopy, htmp, hframe, hregs⟩ :=
    SubexpScopeMembershipProgram.member_eval [false] records start h0 h1 h2 h3 h4
  let e0 := cleared 0 e
  let e1 := cleared 1 e0
  let e2 := cleared 2 e1
  have hl1 : e0.stacks 1 = [decide ([false] ∈ records)] := by
    simpa [e0, cleared] using hout
  have hl2 : e1.stacks 2 = [false] := by
    simpa [e1, e0, cleared, h2] using hquery
  have hc1 : Eval (clear 1) 5 e0 e1 := by
    simpa only [hl1, List.length_cons, List.length_nil] using clear_eval 1 e0
  have hc2 : Eval (clear 2) 5 e1 e2 := by
    simpa only [hl2, List.length_cons, List.length_nil] using clear_eval 2 e1
  have hstacks : e2.stacks = d.stacks := by
    funext i
    fin_cases i
    · simp [e2, e1, e0, cleared, hr.1 0 (by decide)]
    · simp [e2, e1, e0, cleared, hr.1 1 (by decide)]
    · simp [e2, e1, e0, cleared, hr.1 2 (by decide)]
    · simp [e2, e1, e0, cleared, hcopy, hr.1 3 (by decide)]
    · simp [e2, e1, e0, cleared, htmp, hr.1 4 (by decide)]
    · simp [e2, e1, e0, cleared, hframe 5 (by decide), start, queryLoaded, copied]
    · simp [e2, e1, e0, cleared, hframe 6 (by decide), start, queryLoaded, copied]
    · simp [e2, e1, e0, cleared, hframe 7 (by decide), start, queryLoaded, copied]
    · simp [e2, e1, e0, cleared, hframe 8 (by decide), start, queryLoaded, copied]
    · simp [e2, e1, e0, cleared, hframe 9 (by decide), start, queryLoaded, copied]
  have hend : resetResult e2 = result d (decide ([false] ∈ records)) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      by_cases hi0 : i = 0
      · subst i
        simpa [resetResult, result, e2, e1, e0, cleared, readRegs] using hf
      by_cases hi7 : i.val < 7
      · simp [ hi0, hi7]
      · have hi : 7 ≤ i.val := by omega
        have hi1 : i ≠ 1 := by intro hh; subst i; simp at hi
        have hi2 : i ≠ 0 := hi0
        simpa [resetResult, result, hi0, hi7, e2, e1, e0, cleared, readRegs,
          start, queryLoaded, copied, hi1, hi2] using hregs i hi
    · exact hstacks
  have hex := (copyLeaf_eval d hr).seq ((loadQuery_eval (copied d)).seq
    (he.seq ((clear_eval 0 e).seq (hc1.seq (hc2.seq (resetWork_eval e2))))))
  rw [hend] at hex
  refine ⟨(7 * (d.stacks 9).length + 5) + (2 + (t +
    ((2 * (e.stacks 0).length + 3) + (5 + (5 + 7))))), ?_, hex⟩
  simp only [List.length_cons, List.length_nil] at ht
  rw [← hbody] at ht hlen
  omega

def program := StructuredCalls.compiled command (9 : Fin 10) 9

theorem program_runsIn (records : List (List Bool)) (d : Data)
    (hbody : d.stacks 9 = Encoding.encodeList id records) (hr : Ready d) :
    RunsIn program (100 * ((d.stacks 9).length + 1) + 1)
      (d.withPC (some program.entry))
      ((result d (decide ([false] ∈ records))).withPC none) := by
  obtain ⟨t, ht, he⟩ := command_eval records d hbody hr
  exact ⟨t + 1, by omega, compiled_halt_trace he 9 9⟩

theorem empty_record_iff {α : Type*} (encode : α → List Bool) (F : List (List α)) :
    [false] ∈ F.map (Encoding.encodeList encode) ↔ [] ∈ F := by
  constructor
  · intro h
    obtain ⟨C, hC, he⟩ := List.mem_map.mp h
    cases C with
    | nil => exact hC
    | cons x xs => simp [Encoding.encodeList] at he
  · intro h
    exact List.mem_map.mpr ⟨[], h, rfl⟩

theorem formula_empty_mem_iff {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    (∅ : SAT.Clause (Fin n)) ∈ ExecCNF.formulaSet F ↔ [] ∈ F := by
  constructor
  · intro h
    obtain ⟨C, hC, hc⟩ := ExecCNF.mem_formulaSet.mp h
    cases C with
    | nil => exact hC
    | cons x xs => simp [ExecCNF.clauseSet] at hc
  · intro h
    exact ExecCNF.mem_formulaSet.mpr ⟨[], h, rfl⟩

theorem empty_unsatisfiable {n : ℕ} (F : List (List (SAT.Literal (Fin n))))
    (h : [] ∈ F) : ¬ SAT.Satisfiable (ExecCNF.formulaSet F) :=
  SAT.not_satisfiable_of_empty_mem ((formula_empty_mem_iff F).mpr h)

end SubexponentialSAT.SubexpEmptyClauseProgram

end OAI.Algorithms
