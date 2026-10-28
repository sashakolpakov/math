import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgramTrivial
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeCorrect
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
import OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeLeaf

/-! Actual outer-CNF terminal handling. The ambient unary header is retained;
an empty formula emits its full count 2^n, and an empty clause emits zero. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal

open BitProgram StructuredCalls
open scoped BigOperators

abbrev Data := State 80 1220
abbrev Trivial := OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafProgram.Trivial.Data

def classifierStacks : Fin 10 ↪ Fin 1220 :=
  (Fin.castAddEmb 1210).trans ((Equiv.swap (9 : Fin 1220) 265).toEmbedding)

@[simp] theorem classifierStacks_body : classifierStacks 9 = 265 := by decide

theorem classifierStacks_low (i : Fin 10) (hi : i.val < 9) :
    classifierStacks i = Fin.castAdd 1210 i := by
  change Equiv.swap (9 : Fin 1220) 265 (Fin.castAdd 1210 i) = _
  apply Equiv.swap_apply_of_ne_of_ne
  · intro h
    have hv : i.val = 9 := congrArg Fin.val h
    omega
  · intro h
    have hv : i.val = 265 := congrArg Fin.val h
    omega

def classifier : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram SqrtLog.LeafProgram.Trivial.program
    (Fin.castAdd 70) classifierStacks)

noncomputable def classified (a : Data) (records : List (List Bool)) : Data :=
  embedState (Fin.castAdd 70) classifierStacks a
    (SqrtLog.LeafProgram.Trivial.result
      (projectState (Fin.castAdd 70) classifierStacks a) records)

structure Ready (a : Data) : Prop where
  low : ∀ i : Fin 1220, i.val < 5 → a.stacks i = []
  scratch : a.stacks 8 = []

theorem classifier_eval (a : Data) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records) (hready : Ready a) :
    ∃ steps, steps ≤ 100 * ((a.stacks 265).length + 1) + 3 ∧
      Eval classifier steps a (classified a records) := by
  have hb : (projectState (Fin.castAdd 70) classifierStacks a).stacks 9 =
      Encoding.encodeList id records := by simpa [projectState] using hbody
  have hr : SubexpEmptyClauseProgram.Ready
      (projectState (Fin.castAdd 70) classifierStacks a) := by
    constructor
    · intro i hi
      simpa [projectState, classifierStacks_low i (by omega)] using
        hready.1 (Fin.castAdd 1210 i) hi
    · simpa [projectState, classifierStacks_low 8 (by decide)] using hready.2
  obtain ⟨steps, hs, ht⟩ := SqrtLog.LeafProgram.Trivial.program_run _ records hb hr
  refine ⟨steps, ?_, eval_call_from_state _ _ _ a
    (Fin.castAdd_injective 10 70) classifierStacks.injective ht⟩
  simpa [projectState] using hs

theorem classified_stacks (a : Data) (records : List (List Bool)) :
    (classified a records).stacks = a.stacks := by
  funext i
  by_cases hi : ∃ j, classifierStacks j = i
  · obtain ⟨j, rfl⟩ := hi
    exact embedState_stack _ _ _ _ classifierStacks.injective j
  · exact embedState_stack_frame _ _ _ _ i hi

theorem classified_empty_clause (a : Data) (records : List (List Bool)) :
    (classified a records).regs 0 = decide ([false] ∈ records) := by
  exact (embedState_register _ _ _ _ (Fin.castAdd_injective 10 70) 0).trans
    (SqrtLog.LeafProgram.Trivial.result_empty_clause _ _)

theorem classified_nonempty (a : Data) (records : List (List Bool)) :
    (classified a records).regs 7 = decide (records ≠ []) := by
  exact (embedState_register _ _ _ _ (Fin.castAdd_injective 10 70) 7).trans
    (SqrtLog.LeafProgram.Trivial.result_nonempty _ _)

def powerRegs : Fin 2 ↪ Fin 80 where
  toFun := ![72, 73]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

def powerStacks : Fin 2 ↪ Fin 1220 where
  toFun := ![268, 263]
  inj' := by intro i j h; fin_cases i <;> fin_cases j <;> simp_all

@[simp] theorem powerRegs_zero : powerRegs 0 = 72 := by decide

@[simp] theorem powerRegs_one : powerRegs 1 = 73 := by decide

@[simp] theorem powerStacks_zero : powerStacks 0 = 268 := by decide

@[simp] theorem powerStacks_one : powerStacks 1 = 263 := by decide

def power : Cmd 80 1220 :=
  .seq (Native.copyWord 258 268 269)
    (.call (ProgramLinking.liftProgram Native.powerProgram powerRegs powerStacks))

noncomputable def powered (a : Data) (n : ℕ) : Data :=
  embedState powerRegs powerStacks (Native.copiedWord 258 268 a)
    (Native.powerState false [] (countWord (2 ^ n)))

theorem power_eval (a : Data) (n : ℕ)
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (houtput : a.stacks 263 = []) (hwork : a.stacks 268 = [])
    (hscratch : a.stacks 269 = []) :
    Eval power (11 * n + 17) a (powered a n) := by
  have hc := Native.copyWord_eval 258 268 269 a (by decide) (by decide) (by decide) hscratch
  let d := Native.copiedWord 258 268 a
  have hp : projectState powerRegs powerStacks d =
      (⟨d.regs ∘ powerRegs, ![Encoding.encodeNat n, []]⟩ : State 2 2) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [projectState, d, Native.copiedWord,
        StackRoutines.copyStacks, hn, hwork, houtput]
  have ht := Native.power_count_trace (d.regs ∘ powerRegs) n
  rw [← hp] at ht
  have he := eval_call_from_state Native.powerProgram powerRegs powerStacks d
    powerRegs.injective powerStacks.injective ht
  have h := hc.seq he
  convert h using 1
  · rfl
  · rw [hn]
    simp only [Encoding.length_encodeNat]
    omega
  · rfl

theorem powered_output (a : Data) (n : ℕ) :
    (powered a n).stacks 263 = countWord (2 ^ n) :=
  embedState_stack _ _ _ _ powerStacks.injective 1

theorem powered_frame (a : Data) (n : ℕ) (hwork : a.stacks 268 = [])
    (i : Fin 1220) (hi : i ≠ 263) : (powered a n).stacks i = a.stacks i := by
  by_cases hw : i = 268
  · subst i
    rw [hwork]
    exact embedState_stack _ _ _ _ powerStacks.injective 0
  · have hport : ¬ ∃ j, powerStacks j = i := by
      rintro ⟨j, rfl⟩
      fin_cases j
      · exact hw rfl
      · exact hi rfl
    rw [powered, embedState_stack_frame _ _ _ _ i hport]
    simp [Native.copiedWord, StackRoutines.copyStacks, hw]

theorem powered_low_regs (a : Data) (n : ℕ) (i : Fin 80) (hi : i.val < 72) :
    (powered a n).regs i = a.regs i := by
  have hport : ¬ ∃ j, powerRegs j = i := by
    rintro ⟨j, rfl⟩
    have hge : 72 ≤ (powerRegs j).val := by
      fin_cases j <;> decide
    omega
  rw [powered, embedState_register_frame _ _ _ _ i hport]
  have h72 : i ≠ 72 := by intro h; have hv : i.val = 72 := congrArg Fin.val h; omega
  have h73 : i ≠ 73 := by intro h; have hv : i.val = 73 := congrArg Fin.val h; omega
  simp [Native.copiedWord, readRegs, h72, h73]

def zero : Cmd 80 1220 :=
  .seq (.base (.atom (.set 72 false))) (.base (.atom (.push 263 72)))

def zeroed (a : Data) : Data :=
  ⟨Function.update a.regs 72 false, Function.update a.stacks 263 (false :: a.stacks 263)⟩

theorem zero_eval (a : Data) : Eval zero 2 a (zeroed a) :=
  .seq (.base (.atom _ _)) (.base (.atom _ _))

/-- Nonterminal leaves pass through with both classifier flags available. -/
def command : Cmd 80 1220 :=
  .seq classifier (.ite 0 zero (.ite 7 (.base .skip) power))

noncomputable def result (a : Data) (n : ℕ) (records : List (List Bool)) : Data :=
  if [false] ∈ records then zeroed (classified a records)
  else if records = [] then powered (classified a records) n
  else classified a records

theorem command_eval (a : Data) (n : ℕ) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records) (hready : Ready a)
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (houtput : a.stacks 263 = []) (hwork : a.stacks 268 = [])
    (hscratch : a.stacks 269 = []) :
    ∃ steps, steps ≤ 100 * ((a.stacks 265).length + 1) + 11 * n + 22 ∧
      Eval command steps a (result a n records) := by
  obtain ⟨steps, hs, hc⟩ := classifier_eval a records hbody hready
  have hzero := classified_empty_clause a records
  have hnonempty := classified_nonempty a records
  by_cases hz : [false] ∈ records
  · refine ⟨steps + 3, by omega, ?_⟩
    rw [result, ite_eq_left hz]
    exact hc.seq (Eval.ite_true (by simpa [hz] using hzero)
      (zero_eval (classified a records)))
  · by_cases he : records = []
    · have hp := power_eval (classified a records) n
        (by simpa [classified_stacks] using hn)
        (by simpa [classified_stacks] using houtput)
        (by simpa [classified_stacks] using hwork)
        (by simpa [classified_stacks] using hscratch)
      refine ⟨steps + (11 * n + 17 + 1 + 1), by omega, ?_⟩
      rw [result, ite_eq_right hz, ite_eq_left he]
      exact hc.seq (Eval.ite_false (by simpa [hz] using hzero)
        (Eval.ite_false (by simpa [he] using hnonempty) hp))
    · refine ⟨steps + 2, by omega, ?_⟩
      rw [result, ite_eq_right hz, ite_eq_right he]
      exact hc.seq (Eval.ite_false (by simpa [hz] using hzero)
        (Eval.ite_true (by simpa [he] using hnonempty)
          (Eval.base (StructuredProgram.Eval.skip (classified a records)))))

theorem result_frame (a : Data) (n : ℕ) (records : List (List Bool))
    (hwork : a.stacks 268 = []) (i : Fin 1220) (hi : i ≠ 263) :
    (result a n records).stacks i = a.stacks i := by
  by_cases hz : [false] ∈ records
  · simp [result, hz, zeroed, hi, classified_stacks]
  · by_cases he : records = []
    · rw [result, ite_eq_right hz, ite_eq_left he, powered_frame _ _ (by
        simpa [classified_stacks] using hwork) i hi, classified_stacks]
    · simp [result, hz, he, classified_stacks]

theorem result_low_regs (a : Data) (n : ℕ) (records : List (List Bool))
    (i : Fin 80) (hi : i.val < 72) :
    (result a n records).regs i = (classified a records).regs i := by
  have h72 : i ≠ 72 := by intro h; have hv : i.val = 72 := congrArg Fin.val h; omega
  by_cases hz : [false] ∈ records
  · simp [result, hz, zeroed, h72]
  · by_cases he : records = []
    · rw [result, ite_eq_right hz, ite_eq_left he]
      exact powered_low_regs (classified a records) n i hi
    · simp [result, hz, he]

def clauseRecords {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) : List (List Bool) :=
  F.map (Encoding.encodeList ExecSunflowerCodeTransport.literalWord)

theorem clauseRecords_body {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    Encoding.encodeList id (clauseRecords F) = ExecQuantitativeSparsify.encodeRawFormula F := by
  simp only [clauseRecords, ExecQuantitativeSparsify.encodeRawFormula,
    ExecSparsifyEncoding.encodeList_map]
  rfl

theorem clauseRecords_empty_clause {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    [false] ∈ clauseRecords F ↔ [] ∈ F := SubexpEmptyClauseProgram.empty_record_iff _ F

@[simp] theorem clauseRecords_nil_iff {n : ℕ} (F : List (List (SAT.Literal (Fin n)))) :
    clauseRecords F = [] ↔ F = [] := by simp [clauseRecords]

theorem result_empty_clause {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n)))) :
    (result a n (clauseRecords F)).regs 0 = decide ([] ∈ F) := by
  rw [result_low_regs _ _ _ 0 (by decide), classified_empty_clause]
  simp only [clauseRecords_empty_clause]

theorem result_nonempty {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n)))) :
    (result a n (clauseRecords F)).regs 7 = decide (F ≠ []) := by
  rw [result_low_regs _ _ _ 7 (by decide), classified_nonempty]
  simp only [ne_eq, clauseRecords_nil_iff]

theorem result_nonterminal {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n))))
    (hclause : [] ∉ F) (hformula : F ≠ []) :
    result a n (clauseRecords F) = classified a (clauseRecords F) := by
  simp [result, clauseRecords_empty_clause, hclause, hformula]

theorem formula_eval {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n))))
    (hbody : a.stacks 265 = ExecQuantitativeSparsify.encodeRawFormula F) (hready : Ready a)
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (houtput : a.stacks 263 = []) (hwork : a.stacks 268 = [])
    (hscratch : a.stacks 269 = []) :
    ∃ steps, steps ≤ 100 * ((a.stacks 265).length + 1) + 11 * n + 22 ∧
      Eval command steps a (result a n (clauseRecords F)) :=
  command_eval a n (clauseRecords F) (hbody.trans (clauseRecords_body F).symm)
    hready hn houtput hwork hscratch

/-- The outer trivial cases produce the full ambient count, including n=0. -/
theorem result_count {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n))))
    (houtput : a.stacks 263 = []) (hterminal : [] ∈ F ∨ F = []) :
    (result a n (clauseRecords F)).stacks 263 =
      countWord (SAT.count (ExecCNF.formulaSet F)) := by
  rcases hterminal with hz | he
  · have hzero : SAT.count (ExecCNF.formulaSet F) = 0 :=
      (SAT.count_eq_zero_iff _).mpr (SubexpEmptyClauseProgram.empty_unsatisfiable F hz)
    simp [result, (clauseRecords_empty_clause F).mpr hz, zeroed,
      classified_stacks, houtput, hzero]
  · subst F
    simp [result, clauseRecords, powered_output]

def program := compiled command 265 263

/-- The all-prefix bound includes every persistent stack from the DFS frame. -/
theorem program_trace (a : Data) (n : ℕ) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records) (hready : Ready a)
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (houtput : a.stacks 263 = []) (hwork : a.stacks 268 = [])
    (hscratch : a.stacks 269 = []) {D : ℕ} (hframe : ∀ i, (a.stacks i).length ≤ D) :
    ∃ steps,
      Trace program steps (a.withPC (some program.entry))
        ((result a n records).withPC none) ∧
      steps ≤ 100 * ((a.stacks 265).length + 1) + 11 * n + 23 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace program prefixSteps (a.withPC (some program.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          1220 * D + 100 * ((a.stacks 265).length + 1) + 11 * n + 23 := by
  obtain ⟨steps, hs, he⟩ := command_eval a n records hbody hready hn houtput hwork hscratch
  have hsize : dataBits (a.withPC (some program.entry)) ≤ 1220 * D := by
    change ∑ i : Fin 1220, (a.stacks i).length ≤ _
    calc
      _ ≤ ∑ _i : Fin 1220, D := Finset.sum_le_sum (fun i _ => hframe i)
      _ = _ := by simp
  refine ⟨steps + 1, compiled_halt_trace he 265 263, by omega, ?_⟩
  intro prefixSteps intermediate hprefix htrace i
  have h := StructuredSpace.local_stack_bound program hsize
    prefixSteps intermediate hprefix htrace i
  omega

/-- Dispatcher-local temporary cleanup is executed, not assumed at the DFS boundary. -/
def prepare : Cmd 80 1220 :=
  .seq (Native.clearOutput 263)
    (.seq (Native.clearOutput 268) (Native.clearOutput 269))

def prepared (a : Data) : Data :=
  Native.clearOutputState 269 (Native.clearOutputState 268 (Native.clearOutputState 263 a))

theorem prepare_eval (a : Data) :
    Eval prepare
      (2 * (a.stacks 263).length + 2 * (a.stacks 268).length +
        2 * (a.stacks 269).length + 9) a (prepared a) := by
  have h := (Native.clearOutput_eval 263 a).seq
    ((Native.clearOutput_eval 268 (Native.clearOutputState 263 a)).seq
      (Native.clearOutput_eval 269
        (Native.clearOutputState 268 (Native.clearOutputState 263 a))))
  convert h using 1
  · rfl
  · simp [Native.clearOutputState]
    omega
  · rfl

@[simp] theorem prepared_output (a : Data) : (prepared a).stacks 263 = [] := by
  simp [prepared, Native.clearOutputState]

@[simp] theorem prepared_work (a : Data) : (prepared a).stacks 268 = [] := by
  simp [prepared, Native.clearOutputState]

@[simp] theorem prepared_scratch (a : Data) : (prepared a).stacks 269 = [] := by
  simp [prepared, Native.clearOutputState]

theorem prepared_frame (a : Data) (i : Fin 1220)
    (ho : i ≠ 263) (hw : i ≠ 268) (hs : i ≠ 269) :
    (prepared a).stacks i = a.stacks i := by
  simp [prepared, Native.clearOutputState, ho, hw, hs]

theorem prepared_ready (a : Data) (hr : Ready a) : Ready (prepared a) := by
  constructor
  · intro i hi
    rw [prepared_frame a i]
    · exact hr.1 i hi
    · intro h; have hv : i.val = 263 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 268 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 269 := congrArg Fin.val h; omega
  · rw [prepared_frame a 8 (by decide) (by decide) (by decide)]
    exact hr.2

def readyCommand : Cmd 80 1220 := .seq prepare command

noncomputable def readyResult (a : Data) (n : ℕ) (records : List (List Bool)) : Data :=
  result (prepared a) n records

theorem readyCommand_eval (a : Data) (n : ℕ) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records) (hready : Ready a)
    (hn : a.stacks 258 = Encoding.encodeNat n) :
    ∃ steps, steps ≤
      2 * (a.stacks 263).length + 2 * (a.stacks 268).length +
        2 * (a.stacks 269).length + 100 * ((a.stacks 265).length + 1) + 11 * n + 31 ∧
      Eval readyCommand steps a (readyResult a n records) := by
  have hb := prepared_frame a 265 (by decide) (by decide) (by decide)
  have hh := prepared_frame a 258 (by decide) (by decide) (by decide)
  obtain ⟨steps, hs, he⟩ := command_eval (prepared a) n records
    (hb.trans hbody) (prepared_ready a hready) (hh.trans hn)
    (prepared_output a) (prepared_work a) (prepared_scratch a)
  rw [hb] at hs
  exact ⟨_, by omega, (prepare_eval a).seq he⟩

theorem readyResult_count {n : ℕ} (a : Data) (F : List (List (SAT.Literal (Fin n))))
    (hterminal : [] ∈ F ∨ F = []) :
    (readyResult a n (clauseRecords F)).stacks 263 =
      countWord (SAT.count (ExecCNF.formulaSet F)) :=
  result_count (prepared a) F (prepared_output a) hterminal

theorem readyResult_frame (a : Data) (n : ℕ) (records : List (List Bool))
    (i : Fin 1220) (ho : i ≠ 263) (hw : i ≠ 268) (hs : i ≠ 269) :
    (readyResult a n records).stacks i = a.stacks i := by
  rw [readyResult, result_frame _ _ _ (prepared_work a) i ho,
    prepared_frame a i ho hw hs]

@[simp] theorem readyResult_work (a : Data) (n : ℕ) (records : List (List Bool)) :
    (readyResult a n records).stacks 268 = [] := by
  rw [readyResult, result_frame _ _ _ (prepared_work a) 268 (by decide), prepared_work]

@[simp] theorem readyResult_scratch (a : Data) (n : ℕ) (records : List (List Bool)) :
    (readyResult a n records).stacks 269 = [] := by
  rw [readyResult, result_frame _ _ _ (prepared_work a) 269 (by decide), prepared_scratch]

theorem readyResult_empty_clause {n : ℕ} (a : Data)
    (F : List (List (SAT.Literal (Fin n)))) :
    (readyResult a n (clauseRecords F)).regs 0 = decide ([] ∈ F) :=
  result_empty_clause (prepared a) F

theorem readyResult_nonempty {n : ℕ} (a : Data)
    (F : List (List (SAT.Literal (Fin n)))) :
    (readyResult a n (clauseRecords F)).regs 7 = decide (F ≠ []) :=
  result_nonempty (prepared a) F

def readyProgram := compiled readyCommand 265 263

theorem readyProgram_trace (a : Data) (n : ℕ) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records) (hready : Ready a)
    (hn : a.stacks 258 = Encoding.encodeNat n)
    {D : ℕ} (hframe : ∀ i, (a.stacks i).length ≤ D) :
    ∃ steps,
      Trace readyProgram steps (a.withPC (some readyProgram.entry))
        ((readyResult a n records).withPC none) ∧
      steps ≤ 6 * D + 100 * ((a.stacks 265).length + 1) + 11 * n + 32 ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ steps →
        Trace readyProgram prefixSteps (a.withPC (some readyProgram.entry)) intermediate →
        ∀ i, (intermediate.stacks i).length ≤
          1226 * D + 100 * ((a.stacks 265).length + 1) + 11 * n + 32 := by
  obtain ⟨steps, hs, he⟩ := readyCommand_eval a n records hbody hready hn
  have hsize : dataBits (a.withPC (some readyProgram.entry)) ≤ 1220 * D := by
    change ∑ i : Fin 1220, (a.stacks i).length ≤ _
    calc
      _ ≤ ∑ _i : Fin 1220, D := Finset.sum_le_sum (fun i _ => hframe i)
      _ = _ := by simp
  have h263 := hframe 263
  have h268 := hframe 268
  have h269 := hframe 269
  refine ⟨steps + 1, compiled_halt_trace he 265 263, by omega, ?_⟩
  intro prefixSteps intermediate hprefix htrace i
  have h := StructuredSpace.local_stack_bound readyProgram hsize
    prefixSteps intermediate hprefix htrace i
  omega

/-- Only the classifier's local body word contributes to its temporary bound.
The retained DFS frame is bounded by the same unchanged `bound`. -/
theorem classifier_space {steps bound : ℕ} {a b : Data}
    (he : Eval classifier steps a b) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records)
    (hlow : ∀ i : Fin 1220, i.val < 9 → a.stacks i = [])
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hbudget : 101 * (a.stacks 265).length + 103 ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled classifier 256 256) prefixSteps
        (a.withPC (some (compiled classifier 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  let localData := projectState (Fin.castAdd 70) classifierStacks a
  have hstacks : localData.stacks = (StructuredProgram.ioState (r := 10) (9 : Fin 10)
      (a.stacks 265)).stacks := by
    funext i
    by_cases hi : i = 9
    · subst i; simp [localData, projectState]
    · have hil : i.val < 9 := by
        have hil := i.isLt
        have hne : i.val ≠ 9 := fun h => hi (Fin.ext h)
        omega
      simp only [localData, projectState, Function.comp_apply, classifierStacks_low i hil,
        hi, ite_false]
      exact hlow (Fin.castAdd 1210 i) hil
  have hr : SubexpEmptyClauseProgram.Ready localData := by
    constructor
    · intro i hi
      rw [hstacks]
      have hne : i ≠ 9 := by intro h; have hv : i.val = 9 := congrArg Fin.val h; omega
      simp [hne]
    · rw [hstacks]; simp
  obtain ⟨t, ht, hrun⟩ := SqrtLog.LeafProgram.Trivial.program_run localData records
    (by simpa [localData, projectState] using hbody) hr
  have hsize : dataBits (localData.withPC
      (some SqrtLog.LeafProgram.Trivial.program.entry)) ≤ (a.stacks 265).length := by
    simp only [dataBits, stackBits, hstacks]
    have hlen : (fun i : Fin 10 => (if i = 9 then a.stacks 265 else []).length) =
        (fun i : Fin 10 => if i = 9 then (a.stacks 265).length else 0) := by
      funext i
      split_ifs <;> rfl
    rw [hlen]
    simp
  have hlocal : ∀ prefixSteps c, prefixSteps ≤ t →
      Trace SqrtLog.LeafProgram.Trivial.program prefixSteps
        (localData.withPC (some SqrtLog.LeafProgram.Trivial.program.entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro prefixSteps c hprefix htrace i
    have hg := StructuredSpace.local_stack_bound SqrtLog.LeafProgram.Trivial.program hsize
      prefixSteps c hprefix htrace i
    have hb : (localData.stacks 9).length = (a.stacks 265).length := by
      simp [localData, projectState]
    rw [hb] at ht
    omega
  have hcall := eval_call_from_state SqrtLog.LeafProgram.Trivial.program
    (Fin.castAdd 70) classifierStacks a (Fin.castAdd_injective 10 70)
    classifierStacks.injective hrun
  have hsteps : steps = t := StreamResources.eval_steps_eq 256 256 he hcall
  subst steps
  have hinit : ProgramLinking.embedCfg (Fin.castAdd 70) classifierStacks id none
      (a.withPC none) (localData.withPC (some SqrtLog.LeafProgram.Trivial.program.entry)) =
      a.withPC (some (ProgramLinking.liftProgram SqrtLog.LeafProgram.Trivial.program
        (Fin.castAdd 70) classifierStacks).entry) := by
    change (embedState (Fin.castAdd 70) classifierStacks a localData).withPC _ = _
    rw [show embedState (Fin.castAdd 70) classifierStacks a localData = a from
      embedState_project _ _ a (Fin.castAdd_injective 10 70) classifierStacks.injective]
    rfl
  have hglobal := StructuredSpace.liftProgram_stack_bound
    SqrtLog.LeafProgram.Trivial.program (Fin.castAdd 70) classifierStacks (a.withPC none)
    (Fin.castAdd_injective 10 70) classifierStacks.injective hrun hlocal hframe
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call p ht =>
      exact StructuredSpace.call_stack_bound _ (compiled classifier 256 256)
        (siteAddress classifier) (exitAddress classifier) (compiled_site classifier 256 256)
        ht hglobal

def powerCall : Cmd 80 1220 :=
  .call (ProgramLinking.liftProgram Native.powerProgram powerRegs powerStacks)

/-- The power producer's local footprint is independent of retained DFS words. -/
theorem powerCall_space {steps bound : ℕ} {a b : Data}
    (he : Eval powerCall steps a b) (n : ℕ)
    (hn : a.stacks 268 = Encoding.encodeNat n) (hout : a.stacks 263 = [])
    (hframe : ∀ i, (a.stacks i).length ≤ bound) (hbudget : 5 * n + 6 ≤ bound) :
    ∀ prefixSteps c, prefixSteps ≤ steps →
      Trace (compiled powerCall 256 256) prefixSteps
        (a.withPC (some (compiled powerCall 256 256).entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  let localData := projectState powerRegs powerStacks a
  have hp : localData = (⟨localData.regs, ![Encoding.encodeNat n, []]⟩ : State 2 2) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i; fin_cases i <;> simp [localData, projectState, hn, hout]
  have hrun := Native.power_count_trace localData.regs n
  rw [← hp] at hrun
  have hsize : dataBits (localData.withPC (some Native.powerProgram.entry)) ≤ n + 1 := by
    simp [dataBits, stackBits, localData, projectState,
      Fin.sum_univ_two, hn, hout]
  have hlocal : ∀ prefixSteps c, prefixSteps ≤ 4 * n + 5 →
      Trace Native.powerProgram prefixSteps
        (localData.withPC (some Native.powerProgram.entry)) c →
      ∀ i, (c.stacks i).length ≤ bound := by
    intro prefixSteps c hprefix htrace i
    have hg := StructuredSpace.local_stack_bound Native.powerProgram hsize
      prefixSteps c hprefix htrace i
    omega
  have hcall := eval_call_from_state Native.powerProgram powerRegs powerStacks a
    powerRegs.injective powerStacks.injective hrun
  have hsteps : steps = 4 * n + 5 := StreamResources.eval_steps_eq 256 256 he hcall
  subst steps
  have hinit : ProgramLinking.embedCfg powerRegs powerStacks id none (a.withPC none)
      (localData.withPC (some Native.powerProgram.entry)) =
      a.withPC (some (ProgramLinking.liftProgram Native.powerProgram powerRegs powerStacks).entry) := by
    change (embedState powerRegs powerStacks a localData).withPC _ = _
    rw [show embedState powerRegs powerStacks a localData = a from
      embedState_project _ _ a powerRegs.injective powerStacks.injective]
    rfl
  have hglobal := StructuredSpace.liftProgram_stack_bound Native.powerProgram
    powerRegs powerStacks (a.withPC none) powerRegs.injective powerStacks.injective
    hrun hlocal hframe
  rw [hinit] at hglobal
  simp only [Nat.max_self] at hglobal
  cases he with
  | call p ht =>
      exact StructuredSpace.call_stack_bound _ (compiled powerCall 256 256)
        (siteAddress powerCall) (exitAddress powerCall) (compiled_site powerCall 256 256)
        ht hglobal


open DisjointReuse.DFSVisit

/-- Copy and power synthesis retain the caller's same per-stack envelope. -/
theorem power_bounded (a : Data) (n bound : ℕ)
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (houtput : a.stacks 263 = []) (hwork : a.stacks 268 = [])
    (hscratch : a.stacks 269 = [])
    (hframe : ∀ i, (a.stacks i).length ≤ bound) (hbudget : 5 * n + 6 ≤ bound) :
    BoundedEval power (11 * n + 17) a (powered a n) bound := by
  let d := Native.copiedWord 258 268 a
  have hc := Native.copyWord_eval 258 268 269 a (by decide) (by decide) (by decide) hscratch
  have hcopy : BoundedEval (Native.copyWord 258 268 269)
      (7 * (a.stacks 258).length + 5) a d bound :=
    ⟨hc, Native.copyWord_space 258 268 269 hc (by decide) (by decide) (by decide)
      hwork hscratch hframe⟩
  have hp : projectState powerRegs powerStacks d =
      (⟨d.regs ∘ powerRegs, ![Encoding.encodeNat n, []]⟩ : State 2 2) := by
    apply CounterForPrograms.data_ext
    · rfl
    · funext i
      fin_cases i <;> simp [projectState, d, Native.copiedWord,
        StackRoutines.copyStacks, hn, hwork, houtput]
  have ht := Native.power_count_trace (d.regs ∘ powerRegs) n
  rw [← hp] at ht
  have he := eval_call_from_state Native.powerProgram powerRegs powerStacks d
    powerRegs.injective powerStacks.injective ht
  have hpow : BoundedEval powerCall (4 * n + 5) d (powered a n) bound :=
    ⟨he, powerCall_space he n
      (by simp [d, Native.copiedWord, StackRoutines.copyStacks, hn, hwork])
      (by simp [d, Native.copiedWord, StackRoutines.copyStacks, houtput])
      hcopy.final_bound hbudget⟩
  have whole := hcopy.seq hpow
  convert whole using 1
  · rfl
  · rw [hn]
    simp only [Encoding.length_encodeNat]
    omega

private theorem atom_bounded (op : StructuredProgram.Atom 80 1220) (a : Data) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound)
    (hb : ∀ i, ((op.eval a).stacks i).length ≤ bound) :
    BoundedEval (.base (.atom op)) 1 a (op.eval a) bound := by
  refine ⟨.base (.atom op a), ?_⟩
  intro prefixSteps c hp hc
  have hcases : prefixSteps = 0 ∨ prefixSteps = 1 := by omega
  rcases hcases with rfl | rfl
  · cases hc
    exact ha
  · rw [trace_same_length_unique hc (compiled_trace (Eval.base (.atom op a)) 256 256)]
    exact hb

private theorem skip_bounded (a : Data) (bound : ℕ)
    (ha : ∀ i, (a.stacks i).length ≤ bound) :
    BoundedEval (.base .skip) 0 a a bound := by
  refine ⟨.base (.skip a), ?_⟩
  intro prefixSteps c hp hc
  have hz : prefixSteps = 0 := by omega
  subst prefixSteps
  cases hc
  exact ha

theorem zero_bounded (a : Data) (bound : ℕ) (houtput : a.stacks 263 = [])
    (hframe : ∀ i, (a.stacks i).length ≤ bound) (hbudget : 1 ≤ bound) :
    BoundedEval zero 2 a (zeroed a) bound := by
  have first := atom_bounded (.set 72 false) a bound hframe hframe
  have second := atom_bounded (.push 263 72) ((StructuredProgram.Atom.set 72 false).eval a)
    bound first.final_bound (by
      intro i
      by_cases hi : i = 263
      · subst i
        simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr,
          houtput] using hbudget
      · simpa [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr, hi]
          using hframe i)
  exact first.seq second

/-- Dispatcher scratch cleanup is non-growing, including arbitrary old words. -/
theorem prepare_bounded (a : Data) (bound : ℕ)
    (hframe : ∀ i, (a.stacks i).length ≤ bound) :
    BoundedEval prepare
      (2 * (a.stacks 263).length + 2 * (a.stacks 268).length +
        2 * (a.stacks 269).length + 9) a (prepared a) bound := by
  have h1e := Native.clearOutput_eval 263 a
  have h1 : BoundedEval (Native.clearOutput 263) _ a _ bound :=
    ⟨h1e, Native.clearOutput_space 263 h1e hframe⟩
  have h2e := Native.clearOutput_eval 268 (Native.clearOutputState 263 a)
  have h2 : BoundedEval (Native.clearOutput 268) _ _ _ bound :=
    ⟨h2e, Native.clearOutput_space 268 h2e h1.final_bound⟩
  have h3e := Native.clearOutput_eval 269
    (Native.clearOutputState 268 (Native.clearOutputState 263 a))
  have h3 : BoundedEval (Native.clearOutput 269) _ _ _ bound :=
    ⟨h3e, Native.clearOutput_space 269 h3e h2.final_bound⟩
  have whole := h1.seq (h2.seq h3)
  convert whole using 1
  · rfl
  · simp [Native.clearOutputState]
    omega
  · rfl

/-- Every terminal branch retains one fixed bound across arbitrary DFS frames. -/
theorem command_bounded (a : Data) (n bound : ℕ) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records)
    (hlow : ∀ i : Fin 1220, i.val < 9 → a.stacks i = [])
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (houtput : a.stacks 263 = []) (hwork : a.stacks 268 = [])
    (hscratch : a.stacks 269 = [])
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound) :
    ∃ steps, steps ≤ 100 * ((a.stacks 265).length + 1) + 11 * n + 22 ∧
      BoundedEval command steps a (result a n records) bound := by
  have hr : Ready a := ⟨fun i hi => hlow i (by omega), hlow 8 (by decide)⟩
  obtain ⟨steps, hs, hc⟩ := classifier_eval a records hbody hr
  have first : BoundedEval classifier steps a (classified a records) bound :=
    ⟨hc, classifier_space hc records hbody hlow hframe hclassifier⟩
  have hzero := classified_empty_clause a records
  have hnonempty := classified_nonempty a records
  by_cases hz : [false] ∈ records
  · refine ⟨steps + 3, by omega, ?_⟩
    rw [result, ite_eq_left hz]
    exact first.seq ((zero_bounded (classified a records) bound
      (by simpa [classified_stacks] using houtput) first.final_bound (by omega)).ite_true
        (by simpa [hz] using hzero))
  · by_cases hempty : records = []
    · have hp := power_bounded (classified a records) n bound
        (by simpa [classified_stacks] using hn)
        (by simpa [classified_stacks] using houtput)
        (by simpa [classified_stacks] using hwork)
        (by simpa [classified_stacks] using hscratch) first.final_bound hpower
      refine ⟨steps + (11 * n + 17 + 1 + 1), by omega, ?_⟩
      rw [result, ite_eq_right hz, ite_eq_left hempty]
      exact first.seq ((hp.ite_false (by simpa [hempty] using hnonempty)).ite_false
        (by simpa [hz] using hzero))
    · refine ⟨steps + 2, by omega, ?_⟩
      rw [result, ite_eq_right hz, ite_eq_right hempty]
      exact first.seq (((skip_bounded (classified a records) bound first.final_bound).ite_true
        (by simpa [hempty] using hnonempty)).ite_false (by simpa [hz] using hzero))

/-- The complete ready terminal command preserves the same DFS stack bound.
The two local budgets depend only on the body and ambient dimension. -/
theorem readyCommand_bounded (a : Data) (n bound : ℕ) (records : List (List Bool))
    (hbody : a.stacks 265 = Encoding.encodeList id records)
    (hlow : ∀ i : Fin 1220, i.val < 9 → a.stacks i = [])
    (hn : a.stacks 258 = Encoding.encodeNat n)
    (hframe : ∀ i, (a.stacks i).length ≤ bound)
    (hclassifier : 101 * (a.stacks 265).length + 103 ≤ bound)
    (hpower : 5 * n + 6 ≤ bound) :
    ∃ steps, steps ≤ 6 * bound + 100 * ((a.stacks 265).length + 1) + 11 * n + 31 ∧
      BoundedEval readyCommand steps a (readyResult a n records) bound := by
  have first := prepare_bounded a bound hframe
  have hb := prepared_frame a 265 (by decide) (by decide) (by decide)
  have hh := prepared_frame a 258 (by decide) (by decide) (by decide)
  have hl : ∀ i : Fin 1220, i.val < 9 → (prepared a).stacks i = [] := by
    intro i hi
    rw [prepared_frame a i]
    · exact hlow i hi
    · intro h; have hv : i.val = 263 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 268 := congrArg Fin.val h; omega
    · intro h; have hv : i.val = 269 := congrArg Fin.val h; omega
  obtain ⟨steps, hs, second⟩ := command_bounded (prepared a) n bound records
    (hb.trans hbody) hl (hh.trans hn) (prepared_output a) (prepared_work a)
    (prepared_scratch a) first.final_bound (by simpa [hb] using hclassifier) hpower
  rw [hb] at hs
  have h263 := hframe 263
  have h268 := hframe 268
  have h269 := hframe 269
  exact ⟨_, by omega, first.seq second⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NativeTerminal
