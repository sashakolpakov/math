import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.DimensionProgram
import OAI.Algorithms.SubexponentialSAT.SubexpNormalizeProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.CandidateScoreProgram
import OAI.Algorithms.SubexponentialSAT.ProgramFrames

namespace OAI.Algorithms

/-! Ascending framed unary seed indices from a runtime unary seed count. -/

namespace SubexponentialSAT.Subexp.AssignmentSeedRange

open BitProgram StructuredCalls TupleProgram

abbrev Data := State 5 6
abbrev unary (n : ℕ) := List.replicate n true

def state (regs : Fin 5 → Bool) (current : ℕ) (input descending output : List Bool) : Data :=
  ⟨regs, ![input, unary current, [], descending, [], output]⟩

def dimStacks : Fin 5 → Fin 6 := Fin.castAdd 1
theorem dimStacks_injective : Function.Injective dimStacks := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 6 => x.val) h)

def dimProgram := compiled DimensionProgram.enumerate 0 3
abbrev dimensions : Cmd 5 6 := .call (ProgramLinking.liftProgram dimProgram id dimStacks)

theorem dimensions_eval (regs : Fin 5 → Bool) (n : ℕ) :
    ∃ rf, Eval dimensions (DimensionProgram.loopCost 0 n + 1)
      (state regs 0 (unary n) [false] [])
      (state rf n [] (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)) []) := by
  let a : State 5 5 := ⟨regs, ![unary n, [], [], [false], []]⟩
  have ha : DimensionProgram.Ready 0 (unary n) [] a := by
    simp [DimensionProgram.Ready, a, ProgramEncoding.encodeRecords, Encoding.encodeList]
  obtain ⟨b, hb, _, ht⟩ := DimensionProgram.enumerate_eval 0 (unary n) [] a ha
  simp only [List.length_replicate, Nat.zero_add, List.append_nil] at hb ht
  let d := state regs 0 (unary n) [false] []
  have he : embedState id dimStacks d a = d := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id dimStacks_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hf : embedState id dimStacks d b =
      state b.regs n [] (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)) [] := by
    apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id dimStacks_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i
      fin_cases i
      · exact hb.1.symm
      · exact hb.2.1.symm
      · exact hb.2.2.1.symm
      · exact hb.2.2.2.1.symm
      · exact hb.2.2.2.2.symm
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim |
        exact (hi ⟨1, rfl⟩).elim | exact (hi ⟨2, rfl⟩).elim |
        exact (hi ⟨3, rfl⟩).elim
  have h := eval_call_lifted dimProgram id dimStacks d Function.injective_id
    dimStacks_injective (compiled_halt_trace ht 0 3)
  exact ⟨b.regs, by simpa only [dimensions, he, hf] using h⟩

def reverseRegisters : Fin 3 → Fin 5 := Fin.castAdd 2
def reverseStacks : Fin 4 → Fin 6 := ![3, 4, 5, 2]
theorem reverseRegisters_injective : Function.Injective reverseRegisters := by
  intro i j h
  exact Fin.ext (congrArg (fun x : Fin 5 => x.val) h)
theorem reverseStacks_injective : Function.Injective reverseStacks := by decide

abbrev reverse : Cmd 5 6 := .call (ProgramLinking.liftProgram
  SubexpNormalizeProgram.reverseRecordsProgram reverseRegisters reverseStacks)

def reversedRegs (regs : Fin 5 → Bool) : Fin 5 → Bool :=
  fun j => if j = 0 then false else if j = 1 then true else if j = 2 then false else regs j

theorem reverse_eval (regs : Fin 5 → Bool) (n : ℕ) (records : List (List Bool)) :
    ∃ ticks, ticks ≤ 10 * (ProgramEncoding.encodeRecords records).length ∧
      Eval reverse ticks
        (state regs n [] (ProgramEncoding.encodeRecords records) [false])
        (state (reversedRegs regs) n [] [] (ProgramEncoding.encodeRecords records.reverse)) := by
  let a := state regs n [] (ProgramEncoding.encodeRecords records) [false]
  let x := SubexpNormalizeProgram.filterState (regs 0) (regs 1) (regs 2)
    (ProgramEncoding.encodeRecords records) [] [false] []
  let y := SubexpNormalizeProgram.filterState false true false [] []
    (ProgramEncoding.encodeRecords records.reverse) []
  have hx : embedState reverseRegisters reverseStacks a x = a := by
    apply embedState_eq_of_ports _ _ _ _ _ reverseRegisters_injective reverseStacks_injective
    · intro i; fin_cases i <;> rfl
    · intros; rfl
    · intro i; fin_cases i <;> rfl
    · intros; rfl
  have hy : embedState reverseRegisters reverseStacks a y =
      state (reversedRegs regs) n [] [] (ProgramEncoding.encodeRecords records.reverse) := by
    apply embedState_eq_of_ports _ _ _ _ _ reverseRegisters_injective reverseStacks_injective
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim |
        exact (hi ⟨1, rfl⟩).elim | exact (hi ⟨2, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      fin_cases i <;> first | rfl | exact (hi ⟨0, rfl⟩).elim |
        exact (hi ⟨1, rfl⟩).elim | exact (hi ⟨2, rfl⟩).elim
  obtain ⟨ticks, hbound, ht⟩ := SubexpNormalizeProgram.reverseRecords_runsIn
    records [] [] [] (regs 0) (regs 1) (regs 2)
  simp only [List.append_nil] at ht
  have h := eval_call_lifted SubexpNormalizeProgram.reverseRecordsProgram
    reverseRegisters reverseStacks a reverseRegisters_injective reverseStacks_injective
    (a := x) (b := y) ht
  exact ⟨ticks, hbound, by simpa only [reverse, hx, hy] using h⟩

theorem earlierRows_eq (k n : ℕ) :
    DimensionProgram.earlierRows k n = (List.range' k n).reverse.map unary := by
  induction n generalizing k with
  | zero => simp [DimensionProgram.earlierRows]
  | succ n ih =>
      simp only [DimensionProgram.earlierRows, List.range'_succ, List.reverse_cons,
        List.map_append, List.map_singleton, ih]

def seedRecords (n : ℕ) : List Bool :=
  ProgramEncoding.encodeRecords ((List.range n).map unary)

abbrev reset : Cmd 5 6 := .base (CandidateScoreProgram.resetList (List.finRange 5))
abbrev command : Cmd 5 6 := .seq (pushConst 3 0 false)
  (.seq dimensions (.seq (pushConst 5 0 false)
    (.seq reverse (.seq (.call (StackRoutines.clearProgram 1 0 1)) reset))))

def inputState (regs : Fin 5 → Bool) (n : ℕ) : Data := state regs 0 (unary n) [] []
def outputState (n : ℕ) : Data := state (fun _ => false) 0 [] [] (seedRecords n)

def budget (n : ℕ) : ℕ := DimensionProgram.loopCost 0 n +
  10 * (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)).length + 2 * n + 13

theorem budget_le (n : ℕ) : budget n ≤ 60 * (n + 1) ^ 2 := by
  have hlength : (DimensionProgram.earlierRows 0 n).length = n := by
    simp [earlierRows_eq]
  have hwidth : ∀ bits ∈ DimensionProgram.earlierRows 0 n, bits.length ≤ n := by
    intro bits hb
    rw [earlierRows_eq] at hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    have hi' : i < n := by simpa using hi
    simp only [List.length_replicate]
    omega
  have hsize := ProgramEncoding.encodeRecords_length_le
    (DimensionProgram.earlierRows 0 n) n hwidth
  rw [hlength] at hsize
  unfold budget
  rw [DimensionProgram.loopCost_eq]
  nlinarith

theorem command_eval (regs : Fin 5 → Bool) (n : ℕ) :
    ∃ ticks, ticks ≤ budget n ∧ Eval command ticks (inputState regs n) (outputState n) := by
  let a := inputState regs n
  let b := pushedState 3 0 false a
  have hb : b = state b.regs 0 (unary n) [false] [] := by
    apply congrArg (StructuredProgram.State.mk b.regs)
    funext i; fin_cases i <;> rfl
  obtain ⟨rf, hd⟩ := dimensions_eval b.regs n
  rw [← hb] at hd
  let c := state rf n [] (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)) []
  let d := pushedState 5 0 false c
  have he : d = state d.regs n []
      (ProgramEncoding.encodeRecords (DimensionProgram.earlierRows 0 n)) [false] := by
    apply congrArg (StructuredProgram.State.mk d.regs)
    funext i; fin_cases i <;> rfl
  obtain ⟨ticks, hbound, hr⟩ := reverse_eval d.regs n (DimensionProgram.earlierRows 0 n)
  rw [← he] at hr
  have hrecords : (DimensionProgram.earlierRows 0 n).reverse = (List.range n).map unary := by
    simp [earlierRows_eq, List.map_reverse, ← List.range_eq_range']
  rw [hrecords] at hr
  let e := state (reversedRegs d.regs) n [] [] (seedRecords n)
  let f : Data := ⟨readRegs e.regs 0 1 none, StackRoutines.clearStacks 1 e.stacks⟩
  have h1 := pushConst_eval 3 0 false a
  have h3 := pushConst_eval 5 0 false c
  have h5 := TupleProgram.clear_eval 1 0 1 e
  have h6 := Eval.base (CandidateScoreProgram.resetList_eval (List.finRange 5) f)
  have hout : (⟨CandidateScoreProgram.resetValues (List.finRange 5) f.regs, f.stacks⟩ : Data) =
      outputState n := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; simp [CandidateScoreProgram.resetValues_apply ]
    · funext i; fin_cases i <;> simp [f, e, state, StackRoutines.clearStacks]
  rw [hout] at h6
  have h := h1.seq (hd.seq (h3.seq (hr.seq (h5.seq h6))))
  change Eval command _ a (outputState n) at h
  refine ⟨_, ?_, h⟩
  have he1 : (e.stacks 1).length = n := by simp [e, state]
  simp only [he1, List.length_finRange]
  dsimp [budget]
  omega

def program := compiled command 0 5

theorem program_runsIn (regs : Fin 5 → Bool) (n : ℕ) :
    RunsIn program (budget n + 1)
      ((inputState regs n).withPC (some program.entry)) ((outputState n).withPC none) := by
  obtain ⟨ticks, ht, he⟩ := command_eval regs n
  exact ⟨ticks + 1, Nat.add_le_add_right ht 1, compiled_halt_trace he 0 5⟩

end SubexponentialSAT.Subexp.AssignmentSeedRange

end OAI.Algorithms
