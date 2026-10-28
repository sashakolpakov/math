import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ProgramLinking
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace OAI.Algorithms

/-!
# Executable binary counters on Boolean stacks

The head of a stack is the least-significant bit.  Leading zeroes are allowed:
there is no hidden normalization precondition, and zero testing scans the bits.
The arithmetic functions below specify the results of finite instruction-table
programs; the machine execution theorems appear after the specifications.
-/

namespace SubexponentialSAT.CounterPrograms

/-- The unsigned value of a little-endian Boolean stack. -/
def value : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * value bs

@[simp] theorem value_nil : value [] = 0 := rfl
@[simp] theorem value_false_cons (bs : List Bool) : value (false :: bs) = 2 * value bs := by
  simp [value]
@[simp] theorem value_true_cons (bs : List Bool) : value (true :: bs) = 1 + 2 * value bs := rfl

/-- Compatibility with the arithmetic module's identical little-endian convention. -/
theorem value_eq_toNat (bs : List Bool) : value bs = BinaryArithmetic.toNat bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [value, BinaryArithmetic.toNat, BinaryArithmetic.bitVal, ih]

/-- The same finite carry/borrow control works in both directions.  `true` is
increment; `false` is decrement, whose value contract requires positive input. -/
def ripple (carry : Bool) : List Bool → List Bool
  | [] => [carry]
  | b :: bs => if b = carry then (!carry) :: ripple carry bs else carry :: bs

@[simp] theorem ripple_nil (carry : Bool) : ripple carry [] = [carry] := rfl

theorem value_increment (bs : List Bool) : value (ripple true bs) = value bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      cases b <;> simp [ripple, value] at * <;> omega

theorem value_decrement {bs : List Bool} (h : 0 < value bs) :
    value (ripple false bs) + 1 = value bs := by
  induction bs with
  | nil => simp at h
  | cons b bs ih =>
      cases b with
      | false =>
          have hb : 0 < value bs := by simpa using h
          have hi := ih hb
          simp [ripple, value] at *
          omega
      | true => simp [ripple, value]; omega

theorem ripple_length_le (carry : Bool) (bs : List Bool) :
    (ripple carry bs).length ≤ bs.length + 1 := by
  induction bs with
  | nil => simp [ripple]
  | cons b bs ih =>
      simp only [ripple, List.length_cons]
      split_ifs <;> simp_all only [List.length_cons] <;> omega

theorem decrement_length {bs : List Bool} (h : 0 < value bs) :
    (ripple false bs).length = bs.length := by
  induction bs with
  | nil => simp at h
  | cons b bs ih =>
      cases b with
      | false =>
          have hb : 0 < value bs := by simpa using h
          simp [ripple, ih hb]
      | true => simp [ripple]

/-- A direct finite Boolean zero test, valid even for noncanonical encodings. -/
def isZero : List Bool → Bool
  | [] => true
  | b :: bs => (!b) && isZero bs

@[simp] theorem isZero_eq_true_iff (bs : List Bool) : isZero bs = true ↔ value bs = 0 := by
  induction bs with
  | nil => simp [isZero]
  | cons b bs ih => cases b <;> simp [isZero, value, ih]

theorem isZero_eq_false_iff (bs : List Bool) : isZero bs = false ↔ 0 < value bs := by
  rw [Bool.eq_false_iff]
  change ¬ (isZero bs = true) ↔ _
  rw [isZero_eq_true_iff]
  exact Nat.pos_iff_ne_zero.symm


open SubexponentialSAT.BitProgram

/-- Three fixed Boolean registers: current bit, presence bit, and an accumulator. -/
def counterRegs (b p z : Bool) : Fin 3 → Bool :=
  fun i => if i = 0 then b else if i = 1 then p else z

/-- The value stack and one scratch stack; neither stack is part of finite control. -/
def counterStacks (xs ys : List Bool) : Fin 2 → List Bool :=
  fun i => if i = 0 then xs else ys

@[simp] theorem counterRegs_zero (b p z : Bool) : counterRegs b p z 0 = b := rfl
@[simp] theorem counterRegs_one (b p z : Bool) : counterRegs b p z 1 = p := rfl
@[simp] theorem counterRegs_two (b p z : Bool) : counterRegs b p z 2 = z := rfl
@[simp] theorem counterStacks_zero (xs ys : List Bool) : counterStacks xs ys 0 = xs := rfl
@[simp] theorem counterStacks_one (xs ys : List Bool) : counterStacks xs ys 1 = ys := rfl

@[simp] theorem update_counterRegs_zero (b p z v : Bool) :
    Function.update (counterRegs b p z) 0 v = counterRegs v p z := by
  funext i
  fin_cases i <;> simp [counterRegs]

@[simp] theorem update_counterRegs_one (b p z v : Bool) :
    Function.update (counterRegs b p z) 1 v = counterRegs b v z := by
  funext i
  fin_cases i <;> simp [counterRegs]

@[simp] theorem update_counterRegs_two (b p z v : Bool) :
    Function.update (counterRegs b p z) 2 v = counterRegs b p v := by
  funext i
  fin_cases i <;> simp [counterRegs]

@[simp] theorem update_counterStacks_zero (xs ys vs : List Bool) :
    Function.update (counterStacks xs ys) 0 vs = counterStacks vs ys := by
  funext i
  fin_cases i <;> simp [counterStacks]

@[simp] theorem update_counterStacks_one (xs ys vs : List Bool) :
    Function.update (counterStacks xs ys) 1 vs = counterStacks xs vs := by
  funext i
  fin_cases i <;> simp [counterStacks]

def counterCfg {l : ℕ} (q : Fin l) (b p z : Bool) (xs ys : List Bool) : Cfg 3 2 l :=
  ⟨some q, counterRegs b p z, counterStacks xs ys⟩

/-- Eleven fixed labels implement carry/borrow and scratch restoration.
The `carry` parameter is a fixed program bit, not an unbounded control value. -/
abbrev rippleProgram (carry : Bool) : Program 3 2 11 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 5
    | 2 => if carry then .branch 0 3 5 else .branch 0 5 3
    | 3 => .bnot 0 0 4
    | 4 => .push 1 0 0
    | 5 => .set 0 carry 6
    | 6 => .push 0 0 7
    | 7 => .pop 1 0 1 8
    | 8 => .branch 1 9 10
    | 9 => .push 0 0 7
    | _ => .halt

@[simp] theorem ripple_step0_nil (c b p z : Bool) (ys : List Bool) :
    step (rippleProgram c) (counterCfg 0 b p z [] ys) =
      some (counterCfg 1 false false z [] ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem ripple_step0_cons (c b p z a : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 0 b p z (a :: xs) ys) =
      some (counterCfg 1 a true z xs ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem ripple_step1 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 1 b p z xs ys) =
      some (counterCfg (if p then 2 else 5) b p z xs ys) := by
  simp [step, counterCfg, execInstr]
  rfl

@[simp] theorem ripple_step2 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 2 b p z xs ys) =
      some (counterCfg (if b = c then 3 else 5) b p z xs ys) := by
  cases c <;> cases b <;> simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step3 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 3 b p z xs ys) =
      some (counterCfg 4 (!b) p z xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step4 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 4 b p z xs ys) =
      some (counterCfg 0 b p z xs (b :: ys)) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step5 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 5 b p z xs ys) =
      some (counterCfg 6 c p z xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step6 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 6 b p z xs ys) =
      some (counterCfg 7 b p z (b :: xs) ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem ripple_step7_nil (c b p z : Bool) (xs : List Bool) :
    step (rippleProgram c) (counterCfg 7 b p z xs []) =
      some (counterCfg 8 false false z xs []) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem ripple_step7_cons (c b p z a : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 7 b p z xs (a :: ys)) =
      some (counterCfg 8 a true z xs ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem ripple_step8 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 8 b p z xs ys) =
      some (counterCfg (if p then 9 else 10) b p z xs ys) := by
  simp [step, counterCfg, execInstr]
  rfl

@[simp] theorem ripple_step9 (c b p z : Bool) (xs ys : List Bool) :
    step (rippleProgram c) (counterCfg 9 b p z xs ys) =
      some (counterCfg 7 b p z (b :: xs) ys) := by
  simp [step, counterCfg, execInstr]

/-- Exact instruction count of the complete scratch-restoration loop. -/
theorem ripple_restore_trace (c b p z : Bool) (xs ys : List Bool) :
    Trace (rippleProgram c) (3 * ys.length + 2)
      (counterCfg 7 b p z xs ys)
      (counterCfg 10 false false z (ys.reverse ++ xs) []) := by
  induction ys generalizing b p xs with
  | nil =>
      simpa using SubexponentialSAT.Computation.Trace.cons (ripple_step7_nil c b p z xs)
        (SubexponentialSAT.Computation.Trace.cons (ripple_step8 c false false z xs [])
          (SubexponentialSAT.Computation.Trace.refl (counterCfg 10 false false z xs [])))
  | cons a ys ih =>
      have h := SubexponentialSAT.Computation.Trace.cons (ripple_step7_cons c b p z a xs ys)
        (SubexponentialSAT.Computation.Trace.cons (ripple_step8 c a true z xs ys)
          (SubexponentialSAT.Computation.Trace.cons (ripple_step9 c a true z xs ys) (ih a true (a :: xs))))
      convert h using 1
      simp [ List.reverse_cons, List.append_assoc]

/-- Exact instruction count, ending at the halt label before executing halt. -/
def rippleCost (c : Bool) : List Bool → ℕ
  | [] => 6
  | b :: bs => if b = c then rippleCost c bs + 8 else 7

/-- Complete program correctness, allowing arbitrary initial scratch contents.
The old scratch contents are restored to the front of the result in reverse. -/
theorem ripple_trace (c b p z : Bool) (xs ys : List Bool) :
    Trace (rippleProgram c) (rippleCost c xs + 3 * ys.length)
      (counterCfg 0 b p z xs ys)
      (counterCfg 10 false false z (ys.reverse ++ ripple c xs) []) := by
  induction xs generalizing b p ys with
  | nil =>
      have h := SubexponentialSAT.Computation.Trace.cons (ripple_step0_nil c b p z ys)
        (SubexponentialSAT.Computation.Trace.cons (ripple_step1 c false false z [] ys)
          (SubexponentialSAT.Computation.Trace.cons (ripple_step5 c false false z [] ys)
            (SubexponentialSAT.Computation.Trace.cons (ripple_step6 c c false z [] ys)
              (ripple_restore_trace c c false z [c] ys))))
      convert h using 1
      · simp [rippleCost ]
        omega
      · simp [ ripple]
  | cons a xs ih =>
      by_cases ha : a = c
      · subst a
        have h := SubexponentialSAT.Computation.Trace.cons (ripple_step0_cons c b p z c xs ys)
          (SubexponentialSAT.Computation.Trace.cons (ripple_step1 c c true z xs ys)
            (SubexponentialSAT.Computation.Trace.cons (by simp)
              (SubexponentialSAT.Computation.Trace.cons (ripple_step3 c c true z xs ys)
                (SubexponentialSAT.Computation.Trace.cons (ripple_step4 c (!c) true z xs ys)
                  (ih (!c) true ((!c) :: ys))))))
        convert h using 1 <;>
          simp [rippleCost, ripple, List.length_cons, List.reverse_cons, List.append_assoc]
        omega
      · have h := SubexponentialSAT.Computation.Trace.cons (ripple_step0_cons c b p z a xs ys)
          (SubexponentialSAT.Computation.Trace.cons (ripple_step1 c a true z xs ys)
            (SubexponentialSAT.Computation.Trace.cons (by simp [ha])
              (SubexponentialSAT.Computation.Trace.cons (ripple_step5 c a true z xs ys)
                (SubexponentialSAT.Computation.Trace.cons (ripple_step6 c c true z xs ys)
                  (ripple_restore_trace c c true z (c :: xs) ys)))))
        convert h using 1 <;> simp [rippleCost, ripple, ha]
        omega

theorem rippleCost_le (c : Bool) (xs : List Bool) :
    rippleCost c xs ≤ 8 * xs.length + 7 := by
  induction xs with
  | nil => simp [rippleCost]
  | cons a xs ih =>
      simp only [rippleCost, List.length_cons]
      split_ifs <;> omega

/-- Increment has an actual finite-table trace and a linear instruction bound. -/
theorem increment_runs (xs : List Bool) :
    RunsIn (rippleProgram true) (8 * xs.length + 7)
      (counterCfg 0 false false false xs [])
      (counterCfg 10 false false false (ripple true xs) []) := by
  refine ⟨rippleCost true xs, rippleCost_le true xs, ?_⟩
  simpa using ripple_trace true false false false xs []

/-- Decrement executes the same fixed-size table; the positivity precondition
is needed only for its arithmetic interpretation. -/
theorem decrement_runs (xs : List Bool) :
    RunsIn (rippleProgram false) (8 * xs.length + 7)
      (counterCfg 0 false false false xs [])
      (counterCfg 10 false false false (ripple false xs) []) := by
  refine ⟨rippleCost false xs, rippleCost_le false xs, ?_⟩
  simpa using ripple_trace false false false false xs []


@[simp] theorem initial_ripple_eq (c : Bool) (xs : List Bool) :
    initial (rippleProgram c) xs = counterCfg 0 false false false xs [] := by
  simp [initial, counterCfg ]
  constructor
  · funext i
    simp [counterRegs]
  · rfl

theorem ripple_halt_step (c : Bool) (xs : List Bool) :
    step (rippleProgram c) (counterCfg 10 false false false xs []) =
      some (terminal (rippleProgram c) xs) := by
  simp [step, counterCfg, execInstr, terminal, counterRegs, counterStacks]
  constructor
  · funext i
    simp [counterRegs]
  · rfl

/-- Complete execution from the language's actual input convention through halt. -/
theorem ripple_terminal_trace (c : Bool) (xs : List Bool) :
    Trace (rippleProgram c) (rippleCost c xs + 1)
      (initial (rippleProgram c) xs) (terminal (rippleProgram c) (ripple c xs)) := by
  have hbase : Trace (rippleProgram c) (rippleCost c xs)
      (counterCfg 0 false false false xs [])
      (counterCfg 10 false false false (ripple c xs) []) := by
    simpa using ripple_trace c false false false xs []
  have hhalt : Trace (rippleProgram c) 1
      (counterCfg 10 false false false (ripple c xs) [])
      (terminal (rippleProgram c) (ripple c xs)) :=
    .cons (ripple_halt_step c (ripple c xs)) (.refl _)
  simpa only [initial_ripple_eq] using hbase.trans hhalt

theorem ripple_terminal_runs (c : Bool) (xs : List Bool) :
    RunsIn (rippleProgram c) (8 * xs.length + 8)
      (initial (rippleProgram c) xs) (terminal (rippleProgram c) (ripple c xs)) := by
  exact ⟨rippleCost c xs + 1, by have h := rippleCost_le c xs; omega,
    ripple_terminal_trace c xs⟩

theorem increment_correct (xs : List Bool) :
    ∃ output : List Bool, value output = value xs + 1 ∧
      RunsIn (rippleProgram true) (8 * xs.length + 8)
        (initial (rippleProgram true) xs) (terminal (rippleProgram true) output) :=
  ⟨ripple true xs, value_increment xs, ripple_terminal_runs true xs⟩

theorem decrement_correct {xs : List Bool} (h : 0 < value xs) :
    ∃ output : List Bool, value output + 1 = value xs ∧ output.length = xs.length ∧
      RunsIn (rippleProgram false) (8 * xs.length + 8)
        (initial (rippleProgram false) xs) (terminal (rippleProgram false) output) :=
  ⟨ripple false xs, value_decrement h, decrement_length h, ripple_terminal_runs false xs⟩

/-- A ten-label zero test. It preserves the data stack, clears scratch, and
returns its answer in Boolean register 2. -/
abbrev zeroProgram : Program 3 2 10 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .set 2 true 1
    | 1 => .pop 0 0 1 2
    | 2 => .branch 1 3 6
    | 3 => .push 1 0 4
    | 4 => .bnot 0 0 5
    | 5 => .band 2 2 0 1
    | 6 => .pop 1 0 1 7
    | 7 => .branch 1 8 9
    | 8 => .push 0 0 6
    | _ => .halt

@[simp] theorem zero_step0 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 0 b p z xs ys) =
      some (counterCfg 1 b p true xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem zero_step1_nil (b p z : Bool) (ys : List Bool) :
    step zeroProgram (counterCfg 1 b p z [] ys) =
      some (counterCfg 2 false false z [] ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem zero_step1_cons (b p z a : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 1 b p z (a :: xs) ys) =
      some (counterCfg 2 a true z xs ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem zero_step2 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 2 b p z xs ys) =
      some (counterCfg (if p then 3 else 6) b p z xs ys) := by
  simp [step, counterCfg, execInstr]
  rfl

@[simp] theorem zero_step3 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 3 b p z xs ys) =
      some (counterCfg 4 b p z xs (b :: ys)) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem zero_step4 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 4 b p z xs ys) =
      some (counterCfg 5 (!b) p z xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem zero_step5 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 5 b p z xs ys) =
      some (counterCfg 1 b p (z && b) xs ys) := by
  simp [step, counterCfg, execInstr]

@[simp] theorem zero_step6_nil (b p z : Bool) (xs : List Bool) :
    step zeroProgram (counterCfg 6 b p z xs []) =
      some (counterCfg 7 false false z xs []) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem zero_step6_cons (b p z a : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 6 b p z xs (a :: ys)) =
      some (counterCfg 7 a true z xs ys) := by
  simp [step, counterCfg, execInstr, readRegs]

@[simp] theorem zero_step7 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 7 b p z xs ys) =
      some (counterCfg (if p then 8 else 9) b p z xs ys) := by
  simp [step, counterCfg, execInstr]
  rfl

@[simp] theorem zero_step8 (b p z : Bool) (xs ys : List Bool) :
    step zeroProgram (counterCfg 8 b p z xs ys) =
      some (counterCfg 6 b p z (b :: xs) ys) := by
  simp [step, counterCfg, execInstr]

theorem zero_restore_trace (b p z : Bool) (xs ys : List Bool) :
    Trace zeroProgram (3 * ys.length + 2)
      (counterCfg 6 b p z xs ys)
      (counterCfg 9 false false z (ys.reverse ++ xs) []) := by
  induction ys generalizing b p xs with
  | nil =>
      simpa using SubexponentialSAT.Computation.Trace.cons (zero_step6_nil b p z xs)
        (SubexponentialSAT.Computation.Trace.cons (zero_step7 false false z xs [])
          (SubexponentialSAT.Computation.Trace.refl (counterCfg 9 false false z xs [])))
  | cons a ys ih =>
      have h := SubexponentialSAT.Computation.Trace.cons (zero_step6_cons b p z a xs ys)
        (SubexponentialSAT.Computation.Trace.cons (zero_step7 a true z xs ys)
          (SubexponentialSAT.Computation.Trace.cons (zero_step8 a true z xs ys) (ih a true (a :: xs))))
      convert h using 1
      simp [ List.reverse_cons, List.append_assoc]

/-- Exact trace through scan and restore, preserving every scanned data bit. -/
theorem zero_scan_trace (b p z : Bool) (xs ys : List Bool) :
    Trace zeroProgram (8 * xs.length + 3 * ys.length + 4)
      (counterCfg 1 b p z xs ys)
      (counterCfg 9 false false (z && isZero xs) (ys.reverse ++ xs) []) := by
  induction xs generalizing b p z ys with
  | nil =>
      have h := SubexponentialSAT.Computation.Trace.cons (zero_step1_nil b p z ys)
        (SubexponentialSAT.Computation.Trace.cons (zero_step2 false false z [] ys) (zero_restore_trace false false z [] ys))
      convert h using 1 <;> simp [isZero]
  | cons a xs ih =>
      have h := SubexponentialSAT.Computation.Trace.cons (zero_step1_cons b p z a xs ys)
        (SubexponentialSAT.Computation.Trace.cons (zero_step2 a true z xs ys)
          (SubexponentialSAT.Computation.Trace.cons (zero_step3 a true z xs ys)
            (SubexponentialSAT.Computation.Trace.cons (zero_step4 a true z xs (a :: ys))
              (SubexponentialSAT.Computation.Trace.cons (zero_step5 (!a) true z xs (a :: ys))
                (ih (!a) true (z && !a) (a :: ys))))))
      convert h using 1 <;>
        simp [isZero, Bool.and_assoc, List.length_cons, List.reverse_cons, List.append_assoc]
      omega

/-- The zero-test answer, counter preservation, scratch clearing, and cost are
all witnessed by a trace of the executable finite instruction table. -/
theorem zero_trace (xs : List Bool) :
    Trace zeroProgram (8 * xs.length + 5)
      (counterCfg 0 false false false xs [])
      (counterCfg 9 false false (isZero xs) xs []) := by
  have h := SubexponentialSAT.Computation.Trace.cons (zero_step0 false false false xs [])
    (zero_scan_trace false false true xs [])
  simpa [Nat.add_assoc] using h


@[simp] theorem initial_zero_eq (xs : List Bool) :
    initial zeroProgram xs = counterCfg 0 false false false xs [] := by
  simp [initial, counterCfg ]
  constructor
  · funext i
    simp [counterRegs]
  · rfl

theorem zero_initial_trace (xs : List Bool) :
    Trace zeroProgram (8 * xs.length + 5) (initial zeroProgram xs)
      (counterCfg 9 false false (isZero xs) xs []) := by
  simpa only [initial_zero_eq] using zero_trace xs

/-- Specialization of the shared linker to identical data ports. -/
abbrev relabelInstr {r s l m : ℕ} (f : Fin l → Fin m) : Instr r s l → Instr r s m :=
  ProgramLinking.relocateInstr id id f none

def relabelCfg {r s l m : ℕ} (f : Fin l → Fin m) (c : Cfg r s l) : Cfg r s m :=
  ⟨c.pc.map f, c.regs, c.stacks⟩

@[simp] theorem embedCfg_id {r s l m : ℕ} (f : Fin l → Fin m)
    (frame : Cfg r s m) (c : Cfg r s l) :
    ProgramLinking.embedCfg id id f none frame c = relabelCfg f c := by
  rcases c with ⟨pc, regs, stk⟩
  cases pc <;> simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, relabelCfg]

/-- The actual shared linker transfers the trace ending before the exit instruction. -/
theorem relabel_trace_to_exit {r s l m : ℕ} {p : Program r s l} {q : Program r s m}
    (f : Fin l → Fin m) (exit : Fin l) (hhalt : p.code exit = .halt)
    (hcode : ∀ i, i ≠ exit → q.code (f i) = relabelInstr f (p.code i))
    {n : ℕ} {a b : Cfg r s l} (ht : Trace p n a b) (hb : b.pc = some exit) :
    Trace q n (relabelCfg f a) (relabelCfg f b) := by
  have h := ProgramLinking.relocate_trace_to_exit p q id id f none (relabelCfg f a)
    Function.injective_id Function.injective_id exit hhalt hcode ht hb
  simpa only [embedCfg_id] using h

/-- A bounded countdown loop. Labels 0--9 test the counter, 10--19 decrement
it, label 20 is the iteration boundary, and label 21 is the exit. -/
abbrev countdownProgram : Program 3 2 22 where
  inputStack := 0
  outputStack := 0
  entry := 0
  code q := match q.val with
    | 0 => .set 2 true 1
    | 1 => .pop 0 0 1 2
    | 2 => .branch 1 3 6
    | 3 => .push 1 0 4
    | 4 => .bnot 0 0 5
    | 5 => .band 2 2 0 1
    | 6 => .pop 1 0 1 7
    | 7 => .branch 1 8 9
    | 8 => .push 0 0 6
    | 9 => .branch 2 21 10
    | 10 => .pop 0 0 1 11
    | 11 => .branch 1 12 15
    | 12 => .branch 0 15 13
    | 13 => .bnot 0 0 14
    | 14 => .push 1 0 10
    | 15 => .set 0 false 16
    | 16 => .push 0 0 17
    | 17 => .pop 1 0 1 18
    | 18 => .branch 1 19 20
    | 19 => .push 0 0 17
    | 20 => .goto 0
    | _ => .halt

def zeroLabel (i : Fin 10) : Fin 22 := ⟨i.val, by omega⟩
def decrementLabel (i : Fin 11) : Fin 22 := ⟨10 + i.val, by omega⟩

theorem countdown_zero_code (i : Fin 10) (hi : i ≠ 9) :
    countdownProgram.code (zeroLabel i) = relabelInstr zeroLabel (zeroProgram.code i) := by
  fin_cases i <;> simp_all [ zeroLabel, relabelInstr, ProgramLinking.relocateInstr]

theorem countdown_decrement_code (i : Fin 11) (hi : i ≠ 10) :
    countdownProgram.code (decrementLabel i) =
      relabelInstr decrementLabel ((rippleProgram false).code i) := by
  fin_cases i <;> simp_all [ decrementLabel, relabelInstr, ProgramLinking.relocateInstr]

theorem countdown_zero_trace (xs : List Bool) :
    Trace countdownProgram (8 * xs.length + 5)
      (counterCfg 0 false false false xs [])
      (counterCfg 9 false false (isZero xs) xs []) := by
  have h := relabel_trace_to_exit zeroLabel 9 (by rfl)
    countdown_zero_code (zero_trace xs) rfl
  simpa [relabelCfg, counterCfg, zeroLabel] using h

theorem countdown_decrement_trace (xs : List Bool) :
    Trace countdownProgram (rippleCost false xs)
      (counterCfg 10 false false false xs [])
      (counterCfg 20 false false false (ripple false xs) []) := by
  have h := relabel_trace_to_exit decrementLabel 10 (by rfl)
    countdown_decrement_code (ripple_trace false false false false xs []) rfl
  simpa [relabelCfg, counterCfg, decrementLabel] using h

@[simp] theorem countdown_step9 (z : Bool) (xs : List Bool) :
    step countdownProgram (counterCfg 9 false false z xs []) =
      some (counterCfg (if z then 21 else 10) false false z xs []) := by
  simp [step, counterCfg, execInstr]
  rfl

@[simp] theorem countdown_step20 (xs : List Bool) :
    step countdownProgram (counterCfg 20 false false false xs []) =
      some (counterCfg 0 false false false xs []) := by
  simp [step, counterCfg, execInstr]

/-- One positive iteration is a measured trace of the combined table, and
strictly decreases the binary counter while preserving its width. -/
theorem countdown_iteration {xs : List Bool} (hx : 0 < value xs) :
    RunsIn countdownProgram (16 * xs.length + 14)
      (counterCfg 0 false false false xs [])
      (counterCfg 0 false false false (ripple false xs) []) := by
  have hz : isZero xs = false := (isZero_eq_false_iff xs).mpr hx
  have hzrun : RunsIn countdownProgram (8 * xs.length + 5)
      (counterCfg 0 false false false xs [])
      (counterCfg 9 false false false xs []) :=
    ⟨_, le_rfl, by simpa [hz] using countdown_zero_trace xs⟩
  have hbranch : RunsIn countdownProgram 1
      (counterCfg 9 false false false xs [])
      (counterCfg 10 false false false xs []) :=
    ⟨1, le_rfl, .cons (by simp) (.refl _)⟩
  have hdec : RunsIn countdownProgram (8 * xs.length + 7)
      (counterCfg 10 false false false xs [])
      (counterCfg 20 false false false (ripple false xs) []) :=
    ⟨_, rippleCost_le false xs, countdown_decrement_trace xs⟩
  have hreturn : RunsIn countdownProgram 1
      (counterCfg 20 false false false (ripple false xs) [])
      (counterCfg 0 false false false (ripple false xs) []) :=
    ⟨1, le_rfl, .cons (by simp) (.refl _)⟩
  convert ((hzrun.trans hbranch).trans hdec).trans hreturn using 1
  omega

/-- The bounded loop really terminates after repeatedly decrementing its input
counter. Its runtime is polynomial in the binary width and numeric loop bound;
the bound itself is data on the stack, never a program label or register. -/
theorem countdown_runs (xs : List Bool) :
    ∃ ys : List Bool, value ys = 0 ∧ ys.length = xs.length ∧
      RunsIn countdownProgram ((value xs + 1) * (16 * xs.length + 14))
        (counterCfg 0 false false false xs [])
        (counterCfg 21 false false true ys []) := by
  have main : ∀ n : ℕ, ∀ xs : List Bool, value xs = n →
      ∃ ys : List Bool, value ys = 0 ∧ ys.length = xs.length ∧
        RunsIn countdownProgram ((n + 1) * (16 * xs.length + 14))
          (counterCfg 0 false false false xs [])
          (counterCfg 21 false false true ys []) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro xs hv
        by_cases hn : n = 0
        · have hzero : value xs = 0 := hv.trans hn
          have hz : isZero xs = true := (isZero_eq_true_iff xs).mpr hzero
          have htest : Trace countdownProgram (8 * xs.length + 5)
              (counterCfg 0 false false false xs [])
              (counterCfg 9 false false true xs []) := by
            simpa [hz] using countdown_zero_trace xs
          have hexit : Trace countdownProgram 1
              (counterCfg 9 false false true xs [])
              (counterCfg 21 false false true xs []) := .cons (by simp) (.refl _)
          refine ⟨xs, hzero, rfl, ?_⟩
          exact ⟨_, by simp only [hn, zero_add, one_mul]; omega, htest.trans hexit⟩
        · have hpos : 0 < value xs := by omega
          have hdec := value_decrement hpos
          have hlen := decrement_length hpos
          have hlt : value (ripple false xs) < n := by omega
          obtain ⟨ys, hyzero, hylen, hyrun⟩ :=
            ih (value (ripple false xs)) hlt (ripple false xs) rfl
          have hprefix := countdown_iteration hpos
          rw [hlen] at hyrun
          have hdec' : value (ripple false xs) + 1 = n := by omega
          rw [hdec'] at hyrun
          refine ⟨ys, hyzero, hylen.trans hlen, ?_⟩
          convert hprefix.trans hyrun using 1
          ring
  exact main (value xs) xs rfl


/-- Reusable bounded-counter loop rule for an arbitrary actual finite program.
The hypotheses are local measured executions (zero exit and one positive
iteration), not a cost annotation for an uninterpreted mathematical function.
The invariant may track any caller work stacks and registers. -/
theorem boundedCounterLoop {r s l : ℕ} (p : Program r s l) (counter : Fin s)
    (Invariant Post : Cfg r s l → Prop) (iterationCost exitCost : ℕ)
    (zeroExit : ∀ c, Invariant c → value (c.stacks counter) = 0 →
      ∃ d, Post d ∧ RunsIn p exitCost c d)
    (positiveIteration : ∀ c, Invariant c → 0 < value (c.stacks counter) →
      ∃ d, Invariant d ∧ value (d.stacks counter) + 1 = value (c.stacks counter) ∧
        RunsIn p iterationCost c d)
    {initialCfg : Cfg r s l} (hinit : Invariant initialCfg) :
    ∃ finalCfg, Post finalCfg ∧
      RunsIn p (value (initialCfg.stacks counter) * iterationCost + exitCost)
        initialCfg finalCfg := by
  have main : ∀ n : ℕ, ∀ c : Cfg r s l, value (c.stacks counter) = n → Invariant c →
      ∃ d, Post d ∧ RunsIn p (n * iterationCost + exitCost) c d := by
    intro n
    induction n with
    | zero =>
        intro c hv hc
        obtain ⟨d, hd, hrun⟩ := zeroExit c hc hv
        exact ⟨d, hd, by simpa using hrun⟩
    | succ n ih =>
        intro c hv hc
        have hp : 0 < value (c.stacks counter) := by omega
        obtain ⟨c', hc', hvalue, hstep⟩ := positiveIteration c hc hp
        have hv' : value (c'.stacks counter) = n := by omega
        obtain ⟨d, hd, htail⟩ := ih c' hv' hc'
        refine ⟨d, hd, ?_⟩
        convert hstep.trans htail using 1
        ring
  exact main _ initialCfg rfl hinit


/-! ## Deriving a binary counter from an input list -/

/-- Input data, binary count, and increment scratch, all on Boolean stacks. -/
def lengthStacks (data count scratch : List Bool) : Fin 3 → List Bool :=
  fun i => if i = 0 then data else if i = 1 then count else scratch

@[simp] theorem lengthStacks_zero (a b c : List Bool) : lengthStacks a b c 0 = a := rfl
@[simp] theorem lengthStacks_one (a b c : List Bool) : lengthStacks a b c 1 = b := rfl
@[simp] theorem lengthStacks_two (a b c : List Bool) : lengthStacks a b c 2 = c := rfl

@[simp] theorem update_lengthStacks_zero (a b c d : List Bool) :
    Function.update (lengthStacks a b c) 0 d = lengthStacks d b c := by
  funext i
  fin_cases i <;> simp [lengthStacks]

def lengthCfg (q : Fin 14) (b p z : Bool) (data count scratch : List Bool) : Cfg 3 3 14 :=
  ⟨some q, counterRegs b p z, lengthStacks data count scratch⟩

/-- Count a list by consuming one bit and incrementing a binary stack counter.
The program has fourteen fixed labels; the input length is never in control. -/
abbrev lengthProgram : Program 3 3 14 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 13
    | 2 => .pop 1 0 1 3
    | 3 => .branch 1 4 7
    | 4 => .branch 0 5 7
    | 5 => .bnot 0 0 6
    | 6 => .push 2 0 2
    | 7 => .set 0 true 8
    | 8 => .push 1 0 9
    | 9 => .pop 2 0 1 10
    | 10 => .branch 1 11 12
    | 11 => .push 1 0 9
    | 12 => .goto 0
    | _ => .halt

def lengthLabel (i : Fin 11) : Fin 14 := ⟨2 + i.val, by omega⟩

theorem length_increment_code (i : Fin 11) (hi : i ≠ 10) :
    lengthProgram.code (lengthLabel i) =
      ProgramLinking.relocateInstr id Fin.succ lengthLabel none ((rippleProgram true).code i) := by
  fin_cases i <;>
    simp_all [ lengthLabel, ProgramLinking.relocateInstr]

theorem extend_lengthStacks (data count scratch : List Bool) :
    Function.extend (Fin.succ : Fin 2 → Fin 3) (counterStacks count scratch)
      (lengthStacks data [] []) = lengthStacks data count scratch := by
  funext i
  fin_cases i
  · have hn : ¬ ∃ j : Fin 2, j.succ = (0 : Fin 3) := by simp
    change Function.extend (Fin.succ : Fin 2 → Fin 3) (counterStacks count scratch)
      (lengthStacks data [] []) 0 = data
    rw [Function.extend_apply' _ _ _ hn]
    rfl
  · exact (Fin.succ_injective 2).extend_apply _ _ 0
  · exact (Fin.succ_injective 2).extend_apply _ _ 1

@[simp] theorem embed_lengthCfg (q : Fin 11) (b p z : Bool) (data count scratch : List Bool) :
    ProgramLinking.embedCfg id Fin.succ lengthLabel none
      (lengthCfg 0 false false false data [] []) (counterCfg q b p z count scratch) =
        lengthCfg (lengthLabel q) b p z data count scratch := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, counterCfg, lengthCfg,
    extend_lengthStacks]

theorem length_increment_trace (b p : Bool) (data count : List Bool) :
    Trace lengthProgram (rippleCost true count)
      (lengthCfg 2 b p false data count [])
      (lengthCfg 12 false false false data (ripple true count) []) := by
  have h := ProgramLinking.relocate_trace_to_exit (rippleProgram true) lengthProgram
    id Fin.succ lengthLabel none (lengthCfg 0 false false false data [] [])
    Function.injective_id (Fin.succ_injective 2) 10 rfl length_increment_code
    (ripple_trace true b p false count []) rfl
  simpa [lengthLabel] using h

@[simp] theorem length_step0_nil (b p : Bool) (count : List Bool) :
    step lengthProgram (lengthCfg 0 b p false [] count []) =
      some (lengthCfg 1 false false false [] count []) := by
  simp [step, lengthCfg, execInstr, readRegs]

@[simp] theorem length_step0_cons (b p a : Bool) (data count : List Bool) :
    step lengthProgram (lengthCfg 0 b p false (a :: data) count []) =
      some (lengthCfg 1 a true false data count []) := by
  simp [step, lengthCfg, execInstr, readRegs]

@[simp] theorem length_step1 (b p : Bool) (data count : List Bool) :
    step lengthProgram (lengthCfg 1 b p false data count []) =
      some (lengthCfg (if p then 2 else 13) b p false data count []) := by
  simp [step, lengthCfg, execInstr]
  rfl

@[simp] theorem length_step12 (data count : List Bool) :
    step lengthProgram (lengthCfg 12 false false false data count []) =
      some (lengthCfg 0 false false false data count []) := by
  simp [step, lengthCfg, execInstr]

theorem length_iteration (b p a : Bool) (data count : List Bool) (B : ℕ)
    (hB : count.length ≤ B) :
    RunsIn lengthProgram (8 * B + 10)
      (lengthCfg 0 b p false (a :: data) count [])
      (lengthCfg 0 false false false data (ripple true count) []) := by
  have hprefix : Trace lengthProgram 2
      (lengthCfg 0 b p false (a :: data) count [])
      (lengthCfg 2 a true false data count []) :=
    .cons (length_step0_cons b p a data count)
      (.cons (length_step1 a true data count) (.refl _))
  have hsuffix : Trace lengthProgram 1
      (lengthCfg 12 false false false data (ripple true count) [])
      (lengthCfg 0 false false false data (ripple true count) []) :=
    .cons (length_step12 data (ripple true count)) (.refl _)
  refine ⟨2 + rippleCost true count + 1, ?_,
    (hprefix.trans (length_increment_trace a true data count)).trans hsuffix⟩
  have hcost := rippleCost_le true count
  omega

/-- General accumulating count: a pre-existing binary counter gains exactly
one for each consumed input bit. `B` is a proved width bound, not machine state. -/
theorem length_accumulate (data count : List Bool) (B : ℕ)
    (hB : count.length + data.length ≤ B) (b p : Bool) :
    ∃ output : List Bool,
      value output = value count + data.length ∧ output.length ≤ count.length + data.length ∧
      RunsIn lengthProgram (data.length * (8 * B + 10) + 2)
        (lengthCfg 0 b p false data count [])
        (lengthCfg 13 false false false [] output []) := by
  induction data generalizing count b p with
  | nil =>
      refine ⟨count, by simp, by simp, ?_⟩
      refine ⟨2, by simp, ?_⟩
      exact .cons (length_step0_nil b p count)
        (.cons (length_step1 false false [] count) (.refl _))
  | cons a data ih =>
      have hlen := ripple_length_le true count
      have hnext : (ripple true count).length + data.length ≤ B := by
        simp only [List.length_cons] at hB
        omega
      obtain ⟨output, hvalue, hsize, hrun⟩ :=
        ih (ripple true count) hnext false false
      have hcount : count.length ≤ B := by omega
      have hprefix := length_iteration b p a data count B hcount
      refine ⟨output, ?_, ?_, ?_⟩
      · rw [value_increment] at hvalue
        simp only [List.length_cons]
        omega
      · simp only [List.length_cons]
        omega
      · convert hprefix.trans hrun using 1
        simp only [List.length_cons]
        ring

theorem length_halt_step (output : List Bool) :
    step lengthProgram (lengthCfg 13 false false false [] output []) =
      some (terminal lengthProgram output) := by
  simp [step, lengthCfg, execInstr, terminal]
  constructor
  · funext i
    simp [counterRegs]
  · funext i
    fin_cases i <;> simp [lengthStacks]

/-- The utility accepted by callers whose current value/presence bits are dirty.
Only the accumulator bit must start false; both live data bits are overwritten. -/
theorem length_correct_from (b p : Bool) (data : List Bool) :
    ∃ output : List Bool, value output = data.length ∧ output.length ≤ data.length ∧
      RunsIn lengthProgram (data.length * (8 * data.length + 10) + 3)
        (lengthCfg 0 b p false data [] []) (terminal lengthProgram output) := by
  obtain ⟨output, hvalue, hsize, hrun⟩ :=
    length_accumulate data [] data.length (by simp) b p
  have hhalt : RunsIn lengthProgram 1
      (lengthCfg 13 false false false [] output []) (terminal lengthProgram output) :=
    ⟨1, le_rfl, .cons (length_halt_step output) (.refl _)⟩
  refine ⟨output, by simpa using hvalue, by simpa using hsize, ?_⟩
  convert hrun.trans hhalt using 1

@[simp] theorem initial_length_eq (data : List Bool) :
    initial lengthProgram data = lengthCfg 0 false false false data [] [] := by
  simp [initial, lengthCfg]
  constructor
  · funext i
    simp [counterRegs]
  · funext i
    fin_cases i <;> simp [lengthStacks]

/-- A fixed finite program produces the binary representation of the raw input
length with a proved polynomial bound on actual primitive source instructions. -/
theorem length_correct (data : List Bool) :
    ∃ output : List Bool, value output = data.length ∧ output.length ≤ data.length ∧
      RunsIn lengthProgram (data.length * (8 * data.length + 10) + 3)
        (initial lengthProgram data) (terminal lengthProgram output) := by
  simpa only [initial_length_eq] using length_correct_from false false data

end SubexponentialSAT.CounterPrograms

end OAI.Algorithms
