import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.SubexpSymbolicCost

namespace OAI.Algorithms

/-!
# Finite Boolean programs for exponent keys

The key adder below has one fixed sixteen-instruction table.  Its two input
words contain unary-delimited exponents; a third input is a unary output-width
counter.  Each round consumes one counter bit and emits one result bit.  Once
the source adder has ended, further rounds emit zero padding.  It therefore
implements truncation and padding without interpreting a dimension as control
code, and without converting an exponent to an unbounded machine register.
-/

namespace SubexponentialSAT.SubexpExponentProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.SubexpSymbolicCost

/-- Prefix of a word, padded by false bits to exactly the requested width. -/
def padTake (width : ℕ) (bits : List Bool) : List Bool :=
  bits.take width ++ List.replicate (width - bits.length) false

@[simp] theorem padTake_zero (bits : List Bool) : padTake 0 bits = [] := by
  simp [padTake]

@[simp] theorem padTake_nil (width : ℕ) :
    padTake width [] = List.replicate width false := by simp [padTake]

@[simp] theorem padTake_cons (width : ℕ) (b : Bool) (bits : List Bool) :
    padTake (width + 1) (b :: bits) = b :: padTake width bits := by
  simp [padTake]

theorem padTake_length (width : ℕ) (bits : List Bool) :
    (padTake width bits).length = width := by
  simp only [padTake, List.length_append, List.length_take, List.length_replicate]
  omega

def normalizedBits (width : ℕ) (left right : List Bool) : List Bool :=
  padTake width (addIndexBits left right).1

/-- One semantic round, used only to state the refinement of the instruction
table.  All four actions below are implemented by literal stack instructions. -/
structure Advance where
  bit : Bool
  left : List Bool
  right : List Bool
  ticks : ℕ

def advance : List Bool → List Bool → Advance
  | true :: xs, ys => ⟨true, xs, ys, 8⟩
  | false :: xs, true :: ys => ⟨true, false :: xs, ys, 11⟩
  | false :: xs, false :: ys => ⟨false, xs, ys, 12⟩
  | false :: xs, [] => ⟨false, false :: xs, [], 9⟩
  | [], ys => ⟨false, [], ys, 6⟩

theorem advance_ticks_le (left right : List Bool) :
    (advance left right).ticks ≤ 12 := by
  cases left with
  | nil => simp [advance]
  | cons b xs =>
    cases b with
    | true => simp [advance]
    | false =>
      cases right with
      | nil => simp [advance]
      | cons b ys => cases b <;> simp [advance]

/-- Exact result and instruction count of the width-controlled rounds. -/
structure Result where
  bits : List Bool
  left : List Bool
  right : List Bool
  ticks : ℕ

def rounds : ℕ → List Bool → List Bool → Result
  | 0, xs, ys => ⟨[], xs, ys, 3⟩
  | n + 1, xs, ys =>
    let a := advance xs ys
    let rest := rounds n a.left a.right
    ⟨a.bit :: rest.bits, rest.left, rest.right, a.ticks + rest.ticks⟩

theorem rounds_ticks_le (width : ℕ) (left right : List Bool) :
    (rounds width left right).ticks ≤ 12 * width + 3 := by
  induction width generalizing left right with
  | zero => simp [rounds]
  | succ n ih =>
    have ha := advance_ticks_le left right
    have hr := ih (advance left right).left (advance left right).right
    simp only [rounds]
    omega

theorem rounds_bits (width : ℕ) (left right : List Bool) :
    (rounds width left right).bits = normalizedBits width left right := by
  induction width generalizing left right with
  | zero => simp [rounds, normalizedBits]
  | succ n ih =>
    cases left with
    | nil => simp [rounds, advance, ih, normalizedBits, addIndexBits,
        List.replicate_succ]
    | cons b xs =>
      cases b with
      | true => simp [rounds, advance, ih, normalizedBits, addIndexBits]
      | false =>
        cases right with
        | nil => simp [rounds, advance, ih, normalizedBits, addIndexBits,
            List.replicate_succ]
        | cons b ys =>
          cases b <;> simp [rounds, advance, ih, normalizedBits, addIndexBits]

/-- Stack 0: left input; 1: right input; 2: width counter; 3: reversed output.
Both registers are scratch bits.  The table is independent of every input. -/
abbrev keyAddProgram : Program 2 4 16 where
  inputStack := 0
  outputStack := 3
  entry := 0
  code := ![
    .pop 2 0 1 1,
    .branch 1 2 15,
    .peek 0 0 1 3,
    .branch 1 4 12,
    .branch 0 5 7,
    .pop 0 0 1 6,
    .set 0 true 14,
    .peek 1 0 1 8,
    .branch 1 9 12,
    .branch 0 10 11,
    .pop 1 0 1 6,
    .pop 0 0 1 13,
    .set 0 false 14,
    .pop 1 0 1 12,
    .push 3 0 0,
    .halt]

def keyStacks (left right counter output : List Bool) : Fin 4 → List Bool :=
  ![left, right, counter, output]

def keyCfg (pc : Option (Fin 16)) (regs : Fin 2 → Bool)
    (left right counter output : List Bool) : Cfg 2 4 16 :=
  ⟨pc, regs, keyStacks left right counter output⟩

private theorem update_left (xs ys count out next : List Bool) :
    Function.update (keyStacks xs ys count out) 0 next =
      keyStacks next ys count out := by
  funext i; fin_cases i <;> simp [keyStacks]

private theorem update_right (xs ys count out next : List Bool) :
    Function.update (keyStacks xs ys count out) 1 next =
      keyStacks xs next count out := by
  funext i; fin_cases i <;> simp [keyStacks]

private theorem update_counter (xs ys count out next : List Bool) :
    Function.update (keyStacks xs ys count out) 2 next =
      keyStacks xs ys next out := by
  funext i; fin_cases i <;> simp [keyStacks]

private theorem update_output (xs ys count out next : List Bool) :
    Function.update (keyStacks xs ys count out) 3 next =
      keyStacks xs ys count next := by
  funext i; fin_cases i <;> simp [keyStacks]

theorem keyAdd_round (regs : Fin 2 → Bool) (left right counter output : List Bool) :
    ∃ finalRegs, Trace keyAddProgram (advance left right).ticks
      (keyCfg (some 0) regs left right (true :: counter) output)
      (keyCfg (some 0) finalRegs (advance left right).left
        (advance left right).right counter ((advance left right).bit :: output)) := by
  cases left with
  | nil =>
    refine ⟨readRegs regs 0 1 none, ?_⟩
    apply SubexponentialSAT.Computation.Trace.of_iterate
    simp [advance, Function.iterate_succ_apply, step, keyAddProgram, execInstr,
      keyCfg, keyStacks, readRegs, Function.update_apply  ]
    constructor <;> funext i <;> fin_cases i <;> simp
  | cons b xs =>
    cases b with
    | true =>
      refine ⟨readRegs regs 0 1 (some true), ?_⟩
      apply SubexponentialSAT.Computation.Trace.of_iterate
      simp [advance, Function.iterate_succ_apply, step, keyAddProgram, execInstr,
        keyCfg, readRegs, Function.update_apply, keyStacks]
      constructor <;> funext i <;> fin_cases i <;> simp
    | false =>
      cases right with
      | nil =>
        refine ⟨readRegs regs 0 1 none, ?_⟩
        apply SubexponentialSAT.Computation.Trace.of_iterate
        simp [advance, Function.iterate_succ_apply, step, keyAddProgram, execInstr,
          keyCfg, readRegs, Function.update_apply, keyStacks]
        constructor <;> funext i <;> fin_cases i <;> simp
      | cons b ys =>
        refine ⟨readRegs regs 0 1 (some b), ?_⟩
        cases b <;>
          apply SubexponentialSAT.Computation.Trace.of_iterate <;>
          simp [advance, Function.iterate_succ_apply, step, keyAddProgram, execInstr,
            keyCfg, readRegs, Function.update_apply, keyStacks] <;>
          (constructor <;> funext i <;> fin_cases i <;> simp)

theorem keyAdd_exit (regs : Fin 2 → Bool) (left right output : List Bool) :
    Trace keyAddProgram 3
      (keyCfg (some 0) regs left right [] output)
      (keyCfg none (readRegs regs 0 1 none) left right [] output) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, keyAddProgram, execInstr,
    keyCfg, readRegs, Function.update_apply, keyStacks]

/-- Exact execution of the concrete table, including its final halt. -/
theorem keyAdd_trace (width : ℕ) (regs : Fin 2 → Bool)
    (left right output : List Bool) :
    ∃ finalRegs, Trace keyAddProgram (rounds width left right).ticks
      (keyCfg (some 0) regs left right (List.replicate width true) output)
      (keyCfg none finalRegs (rounds width left right).left
        (rounds width left right).right []
        ((normalizedBits width left right).reverse ++ output)) := by
  induction width generalizing regs left right output with
  | zero =>
    refine ⟨readRegs regs 0 1 none, ?_⟩
    simpa [rounds, normalizedBits] using (keyAdd_exit regs left right output)
  | succ n ih =>
    obtain ⟨middleRegs, first⟩ := keyAdd_round regs left right
      (List.replicate n true) output
    obtain ⟨finalRegs, rest⟩ := ih middleRegs (advance left right).left
      (advance left right).right ((advance left right).bit :: output)
    refine ⟨finalRegs, ?_⟩
    have total := first.trans rest
    rw [← rounds_bits] at total ⊢
    simpa [rounds, List.replicate_succ, List.reverse_cons, List.append_assoc] using total

/-- Uniform linear instruction bound; arbitrary accumulator contents survive. -/
theorem keyAdd_runsIn (width : ℕ) (regs : Fin 2 → Bool)
    (left right output : List Bool) :
    ∃ finalRegs, RunsIn keyAddProgram (12 * width + 3)
      (keyCfg (some 0) regs left right (List.replicate width true) output)
      (keyCfg none finalRegs (rounds width left right).left
        (rounds width left right).right []
        ((normalizedBits width left right).reverse ++ output)) := by
  obtain ⟨finalRegs, ht⟩ := keyAdd_trace width regs left right output
  exact ⟨finalRegs, _, rounds_ticks_le width left right, ht⟩

/-- The retained input bounds ensure the full product key fits the output
width; normalization therefore loses no coordinate or U/Z exponent. -/
theorem normalizedBits_fixedKey {D : ℕ} (a b : SymbolicCost.RawIndex D)
    (ha : SymbolicCost.Retained D a) (hb : SymbolicCost.Retained D b) :
    normalizedBits (indexBits D) (fixedKey a) (fixedKey b) = fixedKey (a + b) := by
  simpa only [normalizedBits, padTake, ← normalizeKey_eq] using
    fixedKey_add_correct a b ha hb

theorem keyAdd_fixedKey_runsIn {D : ℕ} (a b : SymbolicCost.RawIndex D)
    (ha : SymbolicCost.Retained D a) (hb : SymbolicCost.Retained D b)
    (regs : Fin 2 → Bool) (output : List Bool) :
    ∃ finalRegs, RunsIn keyAddProgram (12 * indexBits D + 3)
      (keyCfg (some 0) regs (fixedKey a) (fixedKey b)
        (List.replicate (indexBits D) true) output)
      (keyCfg none finalRegs
        (rounds (indexBits D) (fixedKey a) (fixedKey b)).left
        (rounds (indexBits D) (fixedKey a) (fixedKey b)).right []
        ((fixedKey (a + b)).reverse ++ output)) := by
  simpa only [normalizedBits_fixedKey a b ha hb] using
    keyAdd_runsIn (indexBits D) regs (fixedKey a) (fixedKey b) output

/-- Refinement all the way to primitive stack-machine transitions.  The
compiler overhead is a constant of the single sixteen-instruction table. -/
theorem keyAdd_primitive (width : ℕ) (regs : Fin 2 → Bool)
    (left right output : List Bool) :
    ∃ finalRegs, Computation.RunsIn (BitProgram.primitive keyAddProgram).step
      (BitProgram.primitiveOverhead keyAddProgram * (12 * width + 3))
      (BitProgram.primitiveCfg keyAddProgram
        (keyCfg (some 0) regs left right (List.replicate width true) output))
      (BitProgram.primitiveCfg keyAddProgram
        (keyCfg none finalRegs (rounds width left right).left
          (rounds width left right).right []
          ((normalizedBits width left right).reverse ++ output))) := by
  obtain ⟨finalRegs, ht⟩ := keyAdd_runsIn width regs left right output
  exact ⟨finalRegs, BitProgram.primitive_execution keyAddProgram ht⟩

end SubexponentialSAT.SubexpExponentProgram

end OAI.Algorithms
