import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixScanProgram
import OAI.Algorithms.SubexponentialSAT.Subexp.ReadPlan

namespace OAI.Algorithms

/-! Arithmetic meaning of the two physical unary counters and the
compatibility register, including the one-hot color encoding boundary. -/

namespace SubexponentialSAT.Subexp.MatrixScanProgram

open BitProgram StructuredCalls StackRoutines

def same (w : ColorRow) : Bool := decide (w 0 ++ w 1 = w 2 ++ w 3)
def swapped (w : ColorRow) : Bool := decide (w 1 ++ w 0 = w 2 ++ w 3)
def compatible (w : ColorRow) : Bool := same w || swapped w

def unchangedCount : List ColorRow → ℕ
  | [] => 0
  | w :: ws => unchangedCount ws + if same w && !swapped w then 1 else 0

def transposedCount : List ColorRow → ℕ
  | [] => 0
  | w :: ws => transposedCount ws + if swapped w && !same w then 1 else 0

theorem output_count2 (a : Data) (w rests : ColorRow) :
    (MatrixScanStepProgram.output a w rests).stacks 2 =
      if same w && !swapped w then true :: a.stacks 2 else a.stacks 2 := by
  simp +decide [same, swapped, MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts,
    MatrixPositionCountProgram.classified, MatrixPositionProgram.pairMatches,
    MatrixPositionProgram.leftWord, clearStacks]

theorem output_count3 (a : Data) (w rests : ColorRow) :
    (MatrixScanStepProgram.output a w rests).stacks 3 =
      if swapped w && !same w then true :: a.stacks 3 else a.stacks 3 := by
  simp +decide [same, swapped, MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts,
    MatrixPositionCountProgram.classified, MatrixPositionProgram.pairMatches,
    MatrixPositionProgram.leftWord, clearStacks]

theorem output_compatible (a : Data) (w rests : ColorRow) :
    (MatrixScanStepProgram.output a w rests).regs 7 = (a.regs 7 && compatible w) := by
  simp +decide [same, swapped, compatible, MatrixScanStepProgram.output, MatrixScanStepProgram.cleared,
    MatrixScanStepProgram.clearedOne, MatrixScanStepProgram.classified,
    MatrixScanStepProgram.frame, MatrixScanStepProgram.restrict, MatrixScanStepProgram.lowPorts,
    MatrixPositionCountProgram.classified, MatrixPositionProgram.pairMatches,
    MatrixPositionProgram.leftWord, readRegs]

theorem result_count2 (rows : List ColorRow) (a : Data) :
    (result rows a).stacks 2 = List.replicate (unchangedCount rows) true ++ a.stacks 2 := by
  induction rows generalizing a with
  | nil => simp [result, unchangedCount, popped]
  | cons w ws ih =>
      rw [result, ih, output_count2]
      simp only [popped, Function.update_of_ne (by decide : (2 : Fin 23) ≠ 22)]
      cases he : same w && !swapped w <;>
        simp [unchangedCount, he, List.replicate_add, List.append_assoc]

theorem result_count3 (rows : List ColorRow) (a : Data) :
    (result rows a).stacks 3 = List.replicate (transposedCount rows) true ++ a.stacks 3 := by
  induction rows generalizing a with
  | nil => simp [result, transposedCount, popped]
  | cons w ws ih =>
      rw [result, ih, output_count3]
      simp only [popped, Function.update_of_ne (by decide : (3 : Fin 23) ≠ 22)]
      cases he : swapped w && !same w <;>
        simp [transposedCount, he, List.replicate_add, List.append_assoc]

theorem result_compatible (rows : List ColorRow) (a : Data) :
    (result rows a).regs 7 = (a.regs 7 && rows.all compatible) := by
  induction rows generalizing a with
  | nil => simp [result, popped, readRegs]
  | cons w ws ih =>
      rw [result, ih, output_compatible]
      simp [popped, readRegs, Bool.and_assoc]

theorem result_stack_frame (rows : List ColorRow) (a : Data) (j : Fin 23)
    (h2 : j ≠ 2) (h3 : j ≠ 3) (h22 : j ≠ 22)
    (hout : j.val < 13 ∨ 21 ≤ j.val) :
    (result rows a).stacks j = a.stacks j := by
  induction rows generalizing a with
  | nil => simp [result, popped, h22]
  | cons w ws ih =>
      rw [result, ih, output_stack_frame _ _ _ j h2 h3 hout]
      simp [popped, h22]

theorem result_targets (rows : List ColorRow) (a : Data) (width : ℕ)
    (h : Ready a rows width) (i : Fin 4) :
    (result rows a).stacks (MatrixColorReadProgram.target i) = [] := by
  induction rows generalizing a with
  | nil =>
      have ht := h.targets i
      fin_cases i <;> simpa [result, popped, MatrixColorReadProgram.target] using ht
  | cons w ws ih => exact ih _ (output_ready a w ws width h)

theorem result_sources (rows : List ColorRow) (a : Data) (width : ℕ)
    (h : Ready a rows width) (i : Fin 4) :
    (result rows a).stacks (MatrixColorReadProgram.source i) = [] := by
  induction rows generalizing a with
  | nil =>
      have hs := h.sources i
      fin_cases i <;> simpa [result, popped, MatrixColorReadProgram.source] using hs
  | cons w ws ih => exact ih _ (output_ready a w ws width h)

theorem result_counter (rows : List ColorRow) (a : Data) (width : ℕ)
    (h : Ready a rows width) : (result rows a).stacks 22 = [] := by
  induction rows generalizing a with
  | nil =>
      have hz : a.stacks 22 = [] := List.length_eq_zero_iff.mp h.count_length
      simp [result, popped, hz]
  | cons w ws ih => exact ih _ (output_ready a w ws width h)

def resultStacks (rows : List ColorRow) (a : Data) : Fin 23 → List Bool := fun j =>
  if j = 2 then List.replicate (unchangedCount rows) true ++ a.stacks 2
  else if j = 3 then List.replicate (transposedCount rows) true ++ a.stacks 3
  else if 13 ≤ j.val ∧ j.val ≤ 20 then []
  else if j = 22 then [] else a.stacks j

theorem result_stacks (rows : List ColorRow) (a : Data) (width : ℕ)
    (h : Ready a rows width) : (result rows a).stacks = resultStacks rows a := by
  funext j
  fin_cases j
  · simpa [resultStacks] using result_stack_frame rows a 0 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 1 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_count2 rows a
  · simpa [resultStacks] using result_count3 rows a
  · simpa [resultStacks] using result_stack_frame rows a 4 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 5 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 6 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 7 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 8 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 9 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 10 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 11 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_stack_frame rows a 12 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks, MatrixColorReadProgram.target] using result_targets rows a width h 0
  · simpa [resultStacks, MatrixColorReadProgram.target] using result_targets rows a width h 1
  · simpa [resultStacks, MatrixColorReadProgram.target] using result_targets rows a width h 2
  · simpa [resultStacks, MatrixColorReadProgram.target] using result_targets rows a width h 3
  · simpa [resultStacks, MatrixColorReadProgram.source] using result_sources rows a width h 0
  · simpa [resultStacks, MatrixColorReadProgram.source] using result_sources rows a width h 1
  · simpa [resultStacks, MatrixColorReadProgram.source] using result_sources rows a width h 2
  · simpa [resultStacks, MatrixColorReadProgram.source] using result_sources rows a width h 3
  · simpa [resultStacks] using result_stack_frame rows a 21 (by decide) (by decide) (by decide) (by decide)
  · simpa [resultStacks] using result_counter rows a width h

def encodeColor {r : ℕ} (c : Fin r) : List Bool :=
  List.ofFn fun d : Fin r => decide (c = d)

@[simp] theorem encodeColor_length {r : ℕ} (c : Fin r) : (encodeColor c).length = r := by
  simp [encodeColor]

theorem encodeColor_injective {r : ℕ} : Function.Injective (@encodeColor r) := by
  intro c d h
  have he := congrFun (List.ofFn_injective h) c
  simp only [decide_true] at he
  exact (of_decide_eq_true he.symm).symm

@[simp] theorem encodeColor_eq_iff {r : ℕ} (c d : Fin r) :
    encodeColor c = encodeColor d ↔ c = d := encodeColor_injective.eq_iff

theorem encodeColor_pair_eq {r : ℕ} (a b c d : Fin r) :
    encodeColor a ++ encodeColor b = encodeColor c ++ encodeColor d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := List.append_inj h (by simp)
    exact ⟨encodeColor_injective h1, encodeColor_injective h2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

def typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) : ColorRow :=
  ![encodeColor (u.head l), encodeColor (u.slot i l),
    encodeColor (y.head l), encodeColor (y.slot i l)]

@[simp] theorem typedRow_length {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) (j : Fin 4) :
    (typedRow i u y l j).length = r := by
  fin_cases j <;> simp [typedRow]

theorem same_typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) :
    same (typedRow i u y l) = decide (u.head l = y.head l ∧ u.slot i l = y.slot i l) := by
  simp [same, typedRow, encodeColor_pair_eq]

theorem swapped_typedRow {r Q Δ : ℕ} (i : Fin Δ)
    (u y : MulticolorTypes.UniversalType r Q Δ) (l : Fin Q) :
    swapped (typedRow i u y l) = decide (u.slot i l = y.head l ∧ u.head l = y.slot i l) := by
  simp [swapped, typedRow, encodeColor_pair_eq]

end SubexponentialSAT.Subexp.MatrixScanProgram

end OAI.Algorithms
