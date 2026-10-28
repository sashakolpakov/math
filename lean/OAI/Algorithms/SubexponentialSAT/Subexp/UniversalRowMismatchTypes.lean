import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowMismatchProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixInputTypes

namespace OAI.Algorithms

/-! Read the two relevant words from the complete types, generate their
mismatch positions, and restore the temporary extracted words. -/

namespace SubexponentialSAT.Subexp.UniversalRowMismatchTypes

open BitProgram StructuredCalls StackRoutines MulticolorTypes

abbrev Word := List Bool
abbrev Data := State 10 49

def inputRegs : Fin 8 → Fin 10 := Fin.castAdd 2
def inputStacks : Fin 29 → Fin 49 := Fin.castAdd 20
abbrev extract : Cmd 10 49 := .call (ProgramLinking.liftProgram
  MatrixInputProgram.program inputRegs inputStacks)

def filterStacks : Fin 17 → Fin 49 := ![19, 0, 1, 21, 2, 3, 4, 5, 6, 7, 18, 8, 9, 10, 45, 11, 22]
theorem filterStacks_injective : Function.Injective filterStacks := by decide
abbrev filter : Cmd 10 49 := .call (ProgramLinking.liftProgram
  UniversalRowMismatchProgram.program id filterStacks)

abbrev clearRows : Cmd 10 49 :=
  .seq (.call (clearProgram 17 (0 : Fin 10) 1))
    (.seq (.call (clearProgram 18 (0 : Fin 10) 1))
      (.seq (.call (clearProgram 19 (0 : Fin 10) 1))
        (.call (clearProgram 20 (0 : Fin 10) 1))))

abbrev command : Cmd 10 49 := .seq extract (.seq filter clearRows)

variable {r Q Δ : ℕ}

def InputReady (i : Fin Δ) (u y : UniversalType r Q Δ) (a : Data) : Prop :=
  ∀ j : Fin 29, a.stacks (inputStacks j) =
    (MatrixInputTypes.input i u y (a.regs ∘ inputRegs)).stacks j

def extractedStacks (a : Data) (i : Fin Δ) (u y : UniversalType r Q Δ) : Fin 49 → Word :=
  Function.update (Function.update (Function.update (Function.update a.stacks
    17 (ReadPlan.encodeWord u.head)) 18 (ReadPlan.encodeWord (u.slot i)))
    19 (ReadPlan.encodeWord y.head)) 20 (ReadPlan.encodeWord (y.slot i))

def extractBudget (i : Fin Δ) : ℕ :=
  36 * CollisionProgram.typeWidth r Q Δ +
    4 * (i.val + 1) * (14 * (Q * r) + 17) + 203 * (Q * r) + 265

theorem extract_eval (i : Fin Δ) (u y : UniversalType r Q Δ) (a : Data)
    (ha : InputReady i u y a) :
    ∃ n ≤ extractBudget (r := r) (Q := Q) i, ∃ b : Data,
      Eval extract n a b ∧ b.stacks = extractedStacks a i u y := by
  let first := MatrixInputTypes.input i u y (a.regs ∘ inputRegs)
  let last := MatrixInputTypes.output i u y (a.regs ∘ inputRegs)
  obtain ⟨n, hn, ht⟩ := MatrixInputTypes.program_runsIn i u y (a.regs ∘ inputRegs)
  have hin : embedState inputRegs inputStacks a first = a := by
    apply embedState_eq_of_ports _ _ _ _ _ (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 29 20)
    · intros; rfl
    · intros; rfl
    · intro j; exact ha j
    · intros; rfl
  let b := embedState inputRegs inputStacks a last
  have he : Eval extract n a b := by
    have h := eval_call_lifted MatrixInputProgram.program inputRegs inputStacks a
      (Fin.castAdd_injective 8 2) (Fin.castAdd_injective 29 20) (a := first) (b := last) ht
    simpa only [extract, b, hin] using h
  refine ⟨n, hn, b, he, ?_⟩
  funext j
  by_cases hj : ∃ k, inputStacks k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [show b.stacks (inputStacks k) = last.stacks k from
      embedState_stack _ _ _ _ (Fin.castAdd_injective 29 20) k]
    have hk := ha k
    fin_cases k <;> first
      | rfl
      | simpa [last, extractedStacks, inputStacks, MatrixInputTypes.output,
          MatrixInputProgram.outputState, MatrixInputTypes.input, MatrixInputProgram.inputState]
          using hk.symm
  · rw [show b.stacks j = a.stacks j from embedState_stack_frame _ _ _ _ j hj]
    have h17 : j ≠ 17 := fun h => hj ⟨17, h.symm⟩
    have h18 : j ≠ 18 := fun h => hj ⟨18, h.symm⟩
    have h19 : j ≠ 19 := fun h => hj ⟨19, h.symm⟩
    have h20 : j ≠ 20 := fun h => hj ⟨20, h.symm⟩
    simp [extractedStacks, h17, h18, h19, h20]

theorem filter_eval (left right : MulticolorTypes.Word r Q) (a : Data)
    (hl : a.stacks 19 = ReadPlan.encodeWord left)
    (hr : a.stacks 18 = ReadPlan.encodeWord right)
    (hw : a.stacks 21 = List.replicate r true)
    (hq : a.stacks 22 = List.replicate Q true)
    (he : ∀ j : Fin 49, j ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 45] → a.stacks j = []) :
    ∃ n ≤ UniversalRowMismatchProgram.budget Q r, ∃ b : Data,
      Eval filter n a b ∧ b.stacks = Function.update a.stacks 45
        (ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
          (MismatchPlanProgram.selectedPositions left right).reverse)) := by
  let first := UniversalRowMismatchProgram.state a.regs (ReadPlan.encodeWord left)
    (ReadPlan.encodeWord right) (List.replicate r true) (List.replicate Q true) [] [] [] []
  obtain ⟨rf, n, hn, ht⟩ := UniversalRowMismatchProgram.word_program_runsIn left right a.regs
  let result := ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
    (MismatchPlanProgram.selectedPositions left right).reverse)
  let last := UniversalRowMismatchProgram.state rf (ReadPlan.encodeWord left)
    (ReadPlan.encodeWord right) (List.replicate r true) (List.replicate Q true) [] [] [] result
  have hports : ∀ k : Fin 17, a.stacks (filterStacks k) = first.stacks k := by
    intro k
    fin_cases k <;> simp [first, UniversalRowMismatchProgram.state, filterStacks, hl, hr, hw, hq,
      he 0 (by simp), he 1 (by simp), he 2 (by simp), he 3 (by simp), he 4 (by simp),
      he 5 (by simp), he 6 (by simp), he 7 (by simp), he 8 (by simp), he 9 (by simp),
      he 10 (by simp), he 11 (by simp), he 45 (by simp)]
  have hin : embedState id filterStacks a first = a := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id filterStacks_injective
    · intros; rfl
    · intro j hj; exact False.elim (hj ⟨j, rfl⟩)
    · intro k; exact hports k
    · intros; rfl
  let b := embedState id filterStacks a last
  have ht' : Eval filter n a b := by
    have h := eval_call_lifted UniversalRowMismatchProgram.program id filterStacks a
      Function.injective_id filterStacks_injective (a := first) (b := last) ht
    simpa only [filter, b, hin] using h
  refine ⟨n, hn, b, ht', ?_⟩
  funext j
  by_cases hj : ∃ k, filterStacks k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [show b.stacks (filterStacks k) = last.stacks k from
      embedState_stack _ _ _ _ filterStacks_injective k]
    have hk := hports k
    fin_cases k <;> first
      | rfl
      | simpa [last, first, UniversalRowMismatchProgram.state, filterStacks, result] using hk.symm
  · rw [show b.stacks j = a.stacks j from embedState_stack_frame _ _ _ _ j hj]
    have h45 : j ≠ 45 := fun h => hj ⟨14, h.symm⟩
    simp [h45]

def cleared (a : Data) (port : Fin 49) : Data :=
  ⟨readRegs a.regs 0 1 none, clearStacks port a.stacks⟩

theorem clearRows_eval (a : Data) :
    Eval clearRows
      (2 * (a.stacks 17).length + 3 + (2 * (a.stacks 18).length + 3 +
        (2 * (a.stacks 19).length + 3 + (2 * (a.stacks 20).length + 3))))
      a (cleared (cleared (cleared (cleared a 17) 18) 19) 20) := by
  have h17 := TupleProgram.clear_eval (17 : Fin 49) (0 : Fin 10) 1 a
  have h18 := TupleProgram.clear_eval (18 : Fin 49) (0 : Fin 10) 1 (cleared a 17)
  have h19 := TupleProgram.clear_eval (19 : Fin 49) (0 : Fin 10) 1 (cleared (cleared a 17) 18)
  have h20 := TupleProgram.clear_eval (20 : Fin 49) (0 : Fin 10) 1
    (cleared (cleared (cleared a 17) 18) 19)
  have h := h17.seq (h18.seq (h19.seq h20))
  simpa [clearRows, cleared, clearStacks] using h

theorem command_eval (i : Fin Δ) (u y : UniversalType r Q Δ) (a : Data)
    (ha : InputReady i u y a) (h45 : a.stacks 45 = []) :
    ∃ n ≤ extractBudget (r := r) (Q := Q) i + UniversalRowMismatchProgram.budget Q r + 8 * (Q * r) + 12,
      ∃ b : Data, Eval command n a b ∧
        b.stacks = Function.update a.stacks 45
          (ProgramEncoding.encodeRecords (MismatchPlanProgram.indexRecords
            (MismatchPlanProgram.selectedPositions y.head (u.slot i)).reverse)) := by
  obtain ⟨ne, hne, b, hextract, hb⟩ := extract_eval i u y a ha
  have haLow (k : Fin 29) := ha k
  obtain ⟨nf, hnf, c, hfilter, hc⟩ := filter_eval y.head (u.slot i) b
    (by simp [hb, extractedStacks]) (by simp [hb, extractedStacks])
    (by simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
      MatrixInputProgram.inputState] using haLow 21)
    (by simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
      MatrixInputProgram.inputState] using haLow 22)
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 0
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 1
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 2
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 3
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 4
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 5
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 6
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 7
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 8
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 9
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 10
      · simpa [hb, extractedStacks, inputStacks, MatrixInputTypes.input,
          MatrixInputProgram.inputState] using haLow 11
      · simpa [hb, extractedStacks] using h45)
  have hclear := clearRows_eval c
  let d := cleared (cleared (cleared (cleared c 17) 18) 19) 20
  refine ⟨_, ?_, d, hextract.seq (hfilter.seq hclear), ?_⟩
  · have hl17 : (c.stacks 17).length = Q * r := by
      simp [hc, hb, extractedStacks, ReadPlan.wordWidth]
    have hl18 : (c.stacks 18).length = Q * r := by
      simp [hc, hb, extractedStacks, ReadPlan.wordWidth]
    have hl19 : (c.stacks 19).length = Q * r := by
      simp [hc, hb, extractedStacks, ReadPlan.wordWidth]
    have hl20 : (c.stacks 20).length = Q * r := by
      simp [hc, hb, extractedStacks, ReadPlan.wordWidth]
    simp only [hl17, hl18, hl19, hl20]
    omega
  · funext k
    have h17 : a.stacks 17 = [] := by
      simpa [inputStacks, MatrixInputTypes.input, MatrixInputProgram.inputState] using haLow 17
    have h18 : a.stacks 18 = [] := by
      simpa [inputStacks, MatrixInputTypes.input, MatrixInputProgram.inputState] using haLow 18
    have h19 : a.stacks 19 = [] := by
      simpa [inputStacks, MatrixInputTypes.input, MatrixInputProgram.inputState] using haLow 19
    have h20 : a.stacks 20 = [] := by
      simpa [inputStacks, MatrixInputTypes.input, MatrixInputProgram.inputState] using haLow 20
    by_cases hk17 : k = 17
    · subst k; simp [d, cleared, clearStacks, hc, hb, extractedStacks, h17]
    by_cases hk18 : k = 18
    · subst k; simp [d, cleared, clearStacks, hc, hb, extractedStacks, h18]
    by_cases hk19 : k = 19
    · subst k; simp [d, cleared, clearStacks, hc, hb, extractedStacks, h19]
    by_cases hk20 : k = 20
    · subst k; simp [d, cleared, clearStacks, hc, hb, extractedStacks, h20]
    · simp [d, cleared, clearStacks, hc, hb, extractedStacks, hk17, hk18, hk19, hk20,
        Function.update_apply]

end SubexponentialSAT.Subexp.UniversalRowMismatchTypes

end OAI.Algorithms
