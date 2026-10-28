import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MismatchPlanSpec
import OAI.Algorithms.SubexponentialSAT.SubexpUnaryRangeProgram

namespace OAI.Algorithms

/-! Generate all positions on tape, then retain the mismatches.  The output
is in descending position order, as required by the prepend-based row loops. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchProgram

open BitProgram StructuredCalls StackRoutines
open MismatchPlanProgram (indexRecords mismatch)

abbrev Word := List Bool
abbrev Regs := Fin 10 → Bool
abbrev Data := State 10 17

def state (regs : Regs) (left right width count index fuel source output : Word) : Data :=
  ⟨regs, ![left, [], [], width, [], index, fuel, [], source, [],
    right, [], [], [], output, [], count]⟩

def rangeMap : Fin 10 → Fin 17 := ![0, 1, 10, 2, 3, 5, 6, 8, 9, 7]
theorem rangeMap_injective : Function.Injective rangeMap := by decide

abbrev rangeCall : Cmd 10 17 := .call (ProgramLinking.liftProgram
  SubexpUnaryRangeProgram.program id rangeMap)

theorem indexPrefix_eq (positions : List ℕ) :
    SubexpUnaryRangeProgram.indexPrefix positions ++ [false] =
      ProgramEncoding.encodeRecords (indexRecords positions) := by
  induction positions with
  | nil => rfl
  | cons i is ih =>
      simpa [SubexpUnaryRangeProgram.indexPrefix, indexRecords,
        ProgramEncoding.encodeRecords, Encoding.encodeList, List.append_assoc] using
        congrArg (fun tail => true :: (Encoding.frame (List.replicate i true) ++ tail)) ih

theorem rangeCall_eval (left right width count out : Word) (regs : Regs) (j n : ℕ) :
    ∃ rf : Regs, Eval rangeCall (SubexpUnaryRangeProgram.steps j n + 2)
      (state regs left right width count (List.replicate j true) (List.replicate n true) out [])
      (state rf left right width count (List.replicate (j + n) true) []
        (SubexpUnaryRangeProgram.indexPrefix (List.range' j n).reverse ++ out) []) := by
  let a := state regs left right width count (List.replicate j true) (List.replicate n true) out []
  let base : SubexpUnaryRangeProgram.Data := ⟨regs, a.stacks ∘ rangeMap⟩
  obtain ⟨rf, ht⟩ := SubexpUnaryRangeProgram.program_trace base regs j n out
  have hin : embedState id rangeMap a (SubexpUnaryRangeProgram.data base regs j n out) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id rangeMap_injective
    · intros; rfl
    · intro k hk; exact False.elim (hk ⟨k, rfl⟩)
    · intro k; fin_cases k <;> rfl
    · intros; rfl
  have hout : embedState id rangeMap a
      (SubexpUnaryRangeProgram.data base rf (j + n) 0
        (SubexpUnaryRangeProgram.indexPrefix (List.range' j n).reverse ++ out)) =
      state rf left right width count (List.replicate (j + n) true) []
        (SubexpUnaryRangeProgram.indexPrefix (List.range' j n).reverse ++ out) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id rangeMap_injective
    · intros; rfl
    · intro k hk; exact False.elim (hk ⟨k, rfl⟩)
    · intro k; fin_cases k <;> rfl
    · intro k hk
      have h5 : k ≠ 5 := fun h => hk ⟨5, by simpa [rangeMap] using h.symm⟩
      have h6 : k ≠ 6 := fun h => hk ⟨6, by simpa [rangeMap] using h.symm⟩
      have h8 : k ≠ 8 := fun h => hk ⟨7, by simpa [rangeMap] using h.symm⟩
      fin_cases k <;> simp_all [state, a]
  have he := eval_call_lifted SubexpUnaryRangeProgram.program id rangeMap a
    Function.injective_id rangeMap_injective ht
  exact ⟨rf, by simpa only [rangeCall, hin, hout] using he⟩

def filterRegs : Fin 8 → Fin 10 := Fin.castAdd 2
def filterStacks : Fin 16 → Fin 17 := Fin.castAdd 1

abbrev filterCall : Cmd 10 17 := .call (ProgramLinking.liftProgram
  MismatchPlanProgram.program filterRegs filterStacks)

def installedRegs (regs : Regs) (rf : Fin 8 → Bool) : Regs :=
  fun j => if h : j.val < 8 then rf ⟨j.val, h⟩ else regs j

theorem filterCall_eval (left right : List Word) (width count : Word)
    (positions : List ℕ) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hvalid : ∀ i ∈ positions, i < left.length ∧ i < right.length) :
    ∃ n ≤ MismatchPlanProgram.sourceBound width.length (indexRecords positions), ∃ rf : Regs,
      Eval filterCall n
        (state regs left.flatten right.flatten width count [] []
          (ProgramEncoding.encodeRecords (indexRecords positions)) [])
        (state rf left.flatten right.flatten width count [] [] []
          (ProgramEncoding.encodeRecords (indexRecords (mismatch left right positions)))) := by
  let a := state regs left.flatten right.flatten width count [] []
    (ProgramEncoding.encodeRecords (indexRecords positions)) []
  obtain ⟨rf, n, hn, ht⟩ := MismatchPlanProgram.program_runsIn left right width positions
    (regs ∘ filterRegs) hleft hright hvalid
  have hin : embedState filterRegs filterStacks a
      (MismatchPlanProgram.state (regs ∘ filterRegs) left.flatten right.flatten width
        (ProgramEncoding.encodeRecords (indexRecords positions)) [] [] []) = a := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 16 1)
    · intros; rfl
    · intros; rfl
    · intro k; fin_cases k <;> rfl
    · intros; rfl
  have hout : embedState filterRegs filterStacks a
      (MismatchPlanProgram.state rf left.flatten right.flatten width [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (mismatch left right positions)))) =
      state (installedRegs regs rf) left.flatten right.flatten width count [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (mismatch left right positions))) := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 16 1)
    · intro k; simp [installedRegs, k.isLt, state ]
    · intro k hk
      have hge : ¬ k.val < 8 := by
        intro h; exact hk ⟨⟨k.val, h⟩, Fin.ext rfl⟩
      simp [installedRegs, state, a, hge]
    · intro k; fin_cases k <;> rfl
    · intro k hk
      have h8 : k ≠ 8 := fun h => hk ⟨8, h.symm⟩
      have h14 : k ≠ 14 := fun h => hk ⟨14, h.symm⟩
      fin_cases k <;> simp_all [state, a]
  have he := eval_call_lifted MismatchPlanProgram.program filterRegs filterStacks a
    (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 16 1) ht
  exact ⟨n, hn, installedRegs regs rf, by simpa only [filterCall, hin, hout] using he⟩

abbrev initializeSource : Cmd 10 17 :=
  .seq (.base (.atom (.set 0 false))) (.base (.atom (.push 8 0)))

abbrev command : Cmd 10 17 :=
  .seq (.call (copyProgram 16 6 15 (0 : Fin 10) 1))
    (.seq initializeSource (.seq rangeCall (.seq (.call (clearProgram 5 (0 : Fin 10) 1)) filterCall)))

abbrev program : Program 10 17 (size command + 1) := compiled command 16 14

def budget (q width : ℕ) : ℕ :=
  9 * q + 13 + SubexpUnaryRangeProgram.steps 0 q +
    MismatchPlanProgram.sourceBound width (indexRecords (List.range q).reverse)

theorem command_eval (left right : List Word) (width : Word) (q : ℕ) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hql : q ≤ left.length) (hqr : q ≤ right.length) :
    ∃ n, n + 1 ≤ budget q width.length ∧ ∃ rf : Regs,
      Eval command n
        (state regs left.flatten right.flatten width (List.replicate q true) [] [] [] [])
        (state rf left.flatten right.flatten width (List.replicate q true) [] [] []
          (ProgramEncoding.encodeRecords (indexRecords (mismatch left right (List.range q).reverse)))) := by
  let a := state regs left.flatten right.flatten width (List.replicate q true) [] [] [] []
  let rc := readRegs regs 0 1 none
  let ri := Function.update rc 0 false
  have hc : Eval (.call (copyProgram 16 6 15 (0 : Fin 10) 1)) (7 * q + 5) a
      (state rc left.flatten right.flatten width (List.replicate q true) []
        (List.replicate q true) [] []) := by
    have h := TupleProgram.copy_eval 16 6 15 (0 : Fin 10) 1
      (by decide) (by decide) (by decide) (by decide) a (by rfl)
    convert h using 1
    · simp [a, state]
    · apply congrArg (StructuredProgram.State.mk rc)
      funext k; fin_cases k <;> simp [a, state, copyStacks]
  have hi : Eval initializeSource 2
      (state rc left.flatten right.flatten width (List.replicate q true) []
        (List.replicate q true) [] [])
      (state ri left.flatten right.flatten width (List.replicate q true) []
        (List.replicate q true) [false] []) := by
    have h := Eval.seq
      (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) false)
        (state rc left.flatten right.flatten width (List.replicate q true) []
          (List.replicate q true) [] [])))
      (Eval.base (StructuredProgram.Eval.atom (.push (8 : Fin 17) (0 : Fin 10))
        ((StructuredProgram.Atom.set (0 : Fin 10) false).eval
          (state rc left.flatten right.flatten width (List.replicate q true) []
            (List.replicate q true) [] []))))
    convert h using 1
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext k; fin_cases k <;> simp [state, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  obtain ⟨rr, hr⟩ := rangeCall_eval left.flatten right.flatten width (List.replicate q true)
    [false] ri 0 q
  have hprefix : SubexpUnaryRangeProgram.indexPrefix (List.range' 0 q).reverse ++ [false] =
      ProgramEncoding.encodeRecords (indexRecords (List.range q).reverse) := by
    rw [← List.range_eq_range']
    exact indexPrefix_eq (List.range q).reverse
  simp only [List.replicate_zero, Nat.zero_add, hprefix] at hr
  let afterRange := state rr left.flatten right.flatten width (List.replicate q true)
    (List.replicate q true) [] (ProgramEncoding.encodeRecords (indexRecords (List.range q).reverse)) []
  have hclear : Eval (.call (clearProgram 5 (0 : Fin 10) 1)) (2 * q + 3) afterRange
      (state (readRegs rr 0 1 none) left.flatten right.flatten width (List.replicate q true)
        [] [] (ProgramEncoding.encodeRecords (indexRecords (List.range q).reverse)) []) := by
    have h := TupleProgram.clear_eval 5 (0 : Fin 10) 1 afterRange
    convert h using 1
    · simp [afterRange, state]
    · apply congrArg (StructuredProgram.State.mk (readRegs rr 0 1 none))
      funext k; fin_cases k <;> simp [afterRange, state, clearStacks]
  obtain ⟨nf, hnf, rf, hf⟩ := filterCall_eval left right width (List.replicate q true)
    (List.range q).reverse (readRegs rr 0 1 none) hleft hright (by
      intro i hi
      have hiq : i < q := List.mem_range.mp (List.mem_reverse.mp hi)
      exact ⟨lt_of_lt_of_le hiq hql, lt_of_lt_of_le hiq hqr⟩)
  refine ⟨_, ?_, rf, hc.seq (hi.seq (hr.seq (hclear.seq hf)))⟩
  dsimp [budget]
  omega

theorem program_runsIn (left right : List Word) (width : Word) (q : ℕ) (regs : Regs)
    (hleft : ∀ row ∈ left, row.length = width.length)
    (hright : ∀ row ∈ right, row.length = width.length)
    (hql : q ≤ left.length) (hqr : q ≤ right.length) :
    ∃ rf : Regs, RunsIn program (budget q width.length)
      ((state regs left.flatten right.flatten width (List.replicate q true) [] [] [] []).withPC
        (some program.entry))
      ((state rf left.flatten right.flatten width (List.replicate q true) [] [] []
        (ProgramEncoding.encodeRecords (indexRecords (mismatch left right (List.range q).reverse)))).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval left right width q regs hleft hright hql hqr
  exact ⟨rf, n + 1, hn, compiled_halt_trace he 16 14⟩

theorem word_program_runsIn {r Q : ℕ} (left right : MulticolorTypes.Word r Q) (regs : Regs) :
    ∃ rf : Regs, RunsIn program (budget Q r)
      ((state regs (ReadPlan.encodeWord left) (ReadPlan.encodeWord right)
        (List.replicate r true) (List.replicate Q true) [] [] [] []).withPC (some program.entry))
      ((state rf (ReadPlan.encodeWord left) (ReadPlan.encodeWord right)
        (List.replicate r true) (List.replicate Q true) [] [] []
        (ProgramEncoding.encodeRecords (indexRecords
          (MismatchPlanProgram.selectedPositions left right).reverse))).withPC none) := by
  obtain ⟨rf, ht⟩ := program_runsIn (MismatchPlanProgram.colorRows left)
    (MismatchPlanProgram.colorRows right) (List.replicate r true) Q regs
    (by simpa using MismatchPlanProgram.colorRows_width left)
    (by simpa using MismatchPlanProgram.colorRows_width right) (by simp) (by simp)
  refine ⟨rf, ?_⟩
  have hreverse : mismatch (MismatchPlanProgram.colorRows left) (MismatchPlanProgram.colorRows right)
      (List.range Q).reverse = (MismatchPlanProgram.selectedPositions left right).reverse := by
    rw [mismatch, List.filter_reverse, ← mismatch, MismatchPlanProgram.mismatch_range]
  simpa only [List.length_replicate, MismatchPlanProgram.colorRows_flatten, hreverse] using ht

end SubexponentialSAT.Subexp.UniversalRowMismatchProgram

end OAI.Algorithms
