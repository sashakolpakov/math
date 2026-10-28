import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.CounterPrograms
import OAI.Algorithms.SubexponentialSAT.BinaryArithmetic
import OAI.Algorithms.SubexponentialSAT.StructuredCalls
import OAI.Algorithms.SubexponentialSAT.StackRoutines
import OAI.Algorithms.SubexponentialSAT.SubexpPackingParameters

namespace OAI.Algorithms

/-!
# Actual finite programs for the growing packing parameters

Numbers are little-endian Boolean stacks, with leading zeroes allowed. The
programs below manipulate only bits and stacks; natural-number quantities in
their specifications and cost bounds are not machine registers.
-/

namespace SubexponentialSAT.SubexpParameterProgram

open SubexponentialSAT.BitProgram
open SubexponentialSAT.CounterPrograms

theorem value_eq_toNat (xs : List Bool) : value xs = BinaryArithmetic.toNat xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => cases b <;> simp [value, BinaryArithmetic.toNat,
      BinaryArithmetic.bitVal, ih]

theorem value_append (xs ys : List Bool) :
    value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      simp only [List.cons_append, value, List.length_cons, ih, pow_succ]
      ring

theorem value_lt_two_pow_length (xs : List Bool) : value xs < 2 ^ xs.length := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
      cases b <;> simp only [value, Bool.toNat_false, Bool.toNat_true,
        List.length_cons, pow_succ] <;> omega

/-- Consume leading zeroes and the first one of a most-significant-first word. -/
def trimTail : List Bool → List Bool
  | [] => []
  | false :: xs => trimTail xs
  | true :: xs => xs

theorem trimTail_length_le (xs : List Bool) : (trimTail xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [trimTail]
  | cons b xs ih => cases b <;> simp [trimTail]; omega

/-- A most-significant one followed by `m` bits has binary logarithm `m`. -/
theorem log2_value_append_true (xs : List Bool) :
    Nat.log2 (value (xs ++ [true])) = xs.length := by
  have hbound := value_lt_two_pow_length xs
  have hpow : 0 < 2 ^ xs.length := Nat.two_pow_pos _
  have hval : value (xs ++ [true]) = value xs + 2 ^ xs.length := by
    simp [value_append, value]
  have hpos : value (xs ++ [true]) ≠ 0 := by omega
  apply Nat.le_antisymm
  · have hlt : value (xs ++ [true]) < 2 ^ (xs.length + 1) := by
      rw [pow_succ]
      omega
    have h := (Nat.log2_lt hpos).mpr hlt
    omega
  · exact (Nat.le_log2 hpos).mpr (by omega)

theorem trimTail_reverse_length (xs : List Bool) :
    (trimTail xs.reverse).length = Nat.log2 (value xs) := by
  induction xs using List.reverseRecOn with
  | nil => simp [trimTail, value]
  | append_singleton xs b ih =>
      cases b with
      | false => simpa [List.reverse_append, trimTail, value_append, value] using ih
      | true => simp [List.reverse_append, trimTail, log2_value_append_true]

theorem value_tail (xs : List Bool) : value xs.tail = value xs / 2 := by
  cases xs with
  | nil => simp [value]
  | cons b xs => cases b <;> simp [value, Nat.add_mul_div_left]

theorem value_drop (k : ℕ) (xs : List Bool) :
    value (xs.drop k) = value xs / 2 ^ k := by
  induction k generalizing xs with
  | zero => simp
  | succ k ih =>
      rw [List.drop_add_one_eq_tail_drop, value_tail, ih, Nat.div_div_eq_div_mul, pow_succ]

/-- Straight-line syntax for a fixed list of primitive operations. -/
def atoms {r s : ℕ} : List (StructuredProgram.Atom r s) → StructuredProgram.Cmd r s
  | [] => .skip
  | op :: ops => .seq (.atom op) (atoms ops)

def runAtoms {r s : ℕ} : List (StructuredProgram.Atom r s) →
    StructuredProgram.State r s → StructuredProgram.State r s
  | [], d => d
  | op :: ops, d => runAtoms ops (op.eval d)

theorem atoms_eval {r s : ℕ} (ops : List (StructuredProgram.Atom r s))
    (d : StructuredProgram.State r s) :
    StructuredProgram.Eval (atoms ops) ops.length d (runAtoms ops d) := by
  induction ops generalizing d with
  | nil => exact .skip d
  | cons op ops ih =>
      simpa only [atoms, runAtoms, List.length_cons, Nat.add_comm 1] using
        StructuredProgram.Eval.seq (.atom op d) (ih (op.eval d))

/-- Four low bits are discarded; the two read registers are then cleared. -/
def shiftFourOps : List (StructuredProgram.Atom 3 3) :=
  [.pop 0 0 1, .pop 0 0 1, .pop 0 0 1, .pop 0 0 1, .set 0 false, .set 1 false]

abbrev shiftFourCmd : StructuredProgram.Cmd 3 3 := atoms shiftFourOps

def shiftFourProgram := StructuredProgram.compiled shiftFourCmd 0 0

theorem shiftFour_eval (xs : List Bool) :
    StructuredProgram.Eval shiftFourCmd 6 (StructuredProgram.ioState 0 xs)
      (StructuredProgram.ioState 0 (xs.drop 4)) := by
  have h := atoms_eval shiftFourOps (StructuredProgram.ioState (r := 3) 0 xs)
  have heq : runAtoms shiftFourOps (StructuredProgram.ioState 0 xs) =
      StructuredProgram.ioState 0 (xs.drop 4) := by
    simp [runAtoms, shiftFourOps, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, StructuredProgram.ioState, execInstr, readRegs]
    constructor
    · funext i
      fin_cases i <;> simp
    · funext i
      fin_cases i <;> simp [List.drop_add_one_eq_tail_drop]
  rw [heq] at h
  simpa [shiftFourCmd, shiftFourOps] using h

theorem shiftFour_trace (xs : List Bool) :
    Trace shiftFourProgram 7 (initial shiftFourProgram xs)
      (terminal shiftFourProgram (xs.drop 4)) :=
  StructuredProgram.compiled_io_trace 0 0 (shiftFour_eval xs)

theorem shiftFour_value (xs : List Bool) : value (xs.drop 4) = value xs / 16 := by
  simpa using value_drop 4 xs

/-! ## Consume a most-significant zero prefix and the leading one -/

abbrev trimProgram : Program 3 3 6 where
  inputStack := 1
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 1 0 1 1
    | 1 => .branch 1 2 3
    | 2 => .branch 0 3 0
    | 3 => .set 0 false 4
    | 4 => .set 1 false 5
    | _ => .halt

def trimCfg (pc : Option (Fin 6)) (b present : Bool) (xs : List Bool) : Cfg 3 3 6 :=
  ⟨pc, counterRegs b present false, lengthStacks [] xs []⟩

@[simp] theorem update_lengthStacks_one (a b c d : List Bool) :
    Function.update (lengthStacks a b c) 1 d = lengthStacks a d c := by
  funext i
  fin_cases i <;> simp [lengthStacks]

theorem trim_finish (b present : Bool) (xs : List Bool) :
    Trace trimProgram 3 (trimCfg (some 3) b present xs) (trimCfg none false false xs) := by
  refine .cons (b := trimCfg (some 4) false present xs) ?_
    (.cons (b := trimCfg (some 5) false false xs) ?_ (.cons ?_ (.refl _)))
  all_goals simp [step, trimCfg, execInstr]

def trimCost : List Bool → ℕ
  | [] => 5
  | false :: xs => trimCost xs + 3
  | true :: _ => 6

theorem trim_trace (xs : List Bool) (b present : Bool) :
    Trace trimProgram (trimCost xs) (trimCfg (some 0) b present xs)
      (trimCfg none false false (trimTail xs)) := by
  induction xs generalizing b present with
  | nil =>
      refine .cons (b := trimCfg (some 1) false false []) ?_
        (.cons ?_ (trim_finish false false []))
      all_goals simp [step, trimCfg, execInstr, readRegs]
  | cons a xs ih =>
      cases a with
      | false =>
          refine .cons (b := trimCfg (some 1) false true xs) ?_
            (.cons (b := trimCfg (some 2) false true xs) ?_
              (.cons ?_ (ih false true)))
          all_goals simp [step, trimCfg, execInstr, readRegs]
      | true =>
          refine .cons (b := trimCfg (some 1) true true xs) ?_
            (.cons (b := trimCfg (some 2) true true xs) ?_
              (.cons ?_ (trim_finish true true xs)))
          all_goals simp [step, trimCfg, execInstr, readRegs]

theorem trimCost_le (xs : List Bool) : trimCost xs ≤ 3 * xs.length + 6 := by
  induction xs with
  | nil => simp [trimCost]
  | cons a xs ih => cases a <;> simp only [trimCost, List.length_cons] <;> omega

theorem trim_complete_trace (xs : List Bool) :
    Trace trimProgram (trimCost xs) (initial trimProgram xs)
      (terminal trimProgram (trimTail xs)) := by
  have hi : initial trimProgram xs = trimCfg (some 0) false false xs := by
    simp [initial, trimCfg ]
    constructor <;> funext i <;> fin_cases i <;> simp [counterRegs, lengthStacks]
  have ht : terminal trimProgram (trimTail xs) = trimCfg none false false (trimTail xs) := by
    simp [terminal, trimCfg ]
    constructor <;> funext i <;> fin_cases i <;> simp [counterRegs, lengthStacks]
  rw [hi, ht]
  exact trim_trace xs false false

theorem trim_complete_runs (xs : List Bool) :
    RunsIn trimProgram (3 * xs.length + 6) (initial trimProgram xs)
      (terminal trimProgram (trimTail xs)) :=
  ⟨trimCost xs, trimCost_le xs, trim_complete_trace xs⟩

/-! ## Concrete input reversal -/

abbrev reverseTransfer : Program 3 3 4 := StackRoutines.transferProgram 0 1 0 1

theorem reverseTransfer_trace (xs : List Bool) :
    Trace reverseTransfer (3 * xs.length + 3) (initial reverseTransfer xs)
      (terminal reverseTransfer xs.reverse) := by
  have h := StackRoutines.transferProgram_trace (r := 3) (s := 3)
    0 1 0 1 (by decide) (by decide) (fun _ => false)
    (fun i => if i = 0 then xs else [])
  have ht : StackRoutines.transferResult (3 : Fin 4) (0 : Fin 3) 1 (0 : Fin 3) 1
      (fun _ => false) (fun i => if i = 0 then xs else []) =
      {terminal reverseTransfer xs.reverse with pc := some 3} := by
    simp [StackRoutines.transferResult, StackRoutines.transferStacks, readRegs]
    funext i
    fin_cases i <;> simp
  have hh : Trace reverseTransfer 1
      {terminal reverseTransfer xs.reverse with pc := some 3}
      (terminal reverseTransfer xs.reverse) := by
    refine .cons ?_ (.refl _)
    simp [step, execInstr, terminal]
  rw [ht] at h
  change Trace reverseTransfer (3 * xs.length + 2) (initial reverseTransfer xs)
    {terminal reverseTransfer xs.reverse with pc := some 3} at h
  simpa only [Nat.add_assoc] using h.trans hh

theorem enter_terminal_eq_initial {r s l m : ℕ}
    (p : Program r s l) (q : Program r s m) (h : p.outputStack = q.inputStack)
    (word : List Bool) :
    ProgramLinking.enter q (terminal p word) = initial q word := by
  simp [ProgramLinking.enter, initial, h]

theorem link_io_runs {r s l m n₁ n₂ : ℕ}
    (p : Program r s l) (q : Program r s m) (h : p.outputStack = q.inputStack)
    (input middle output : List Bool)
    (hp : RunsIn p n₁ (initial p input) (terminal p middle))
    (hq : RunsIn q n₂ (initial q middle) (terminal q output)) :
    RunsIn (ProgramLinking.link p q) (n₁ + n₂)
      (initial (ProgramLinking.link p q) input)
      (terminal (ProgramLinking.link p q) output) := by
  exact ProgramLinking.link_complete_runsIn p q input output hp rfl
    (by simpa only [enter_terminal_eq_initial p q h middle] using hq)

abbrev prepareLogProgram : Program 3 3 10 := ProgramLinking.link reverseTransfer trimProgram

theorem prepareLog_runs (xs : List Bool) :
    RunsIn prepareLogProgram (6 * xs.length + 9)
      (initial prepareLogProgram xs)
      (terminal prepareLogProgram (trimTail xs.reverse)) := by
  have h := link_io_runs reverseTransfer trimProgram rfl xs xs.reverse
    (trimTail xs.reverse) ⟨_, le_rfl, reverseTransfer_trace xs⟩
    (trim_complete_runs xs.reverse)
  convert h using 1
  · simp only [List.length_reverse]
    omega

/-! ## Reindex and call the checked binary word-length counter -/

theorem extend_equiv {α β γ : Type*} (e : α ≃ β) (f : α → γ) (frame : β → γ) :
    Function.extend e f frame = fun b => f (e.symm b) := by
  funext b
  simp

theorem lift_equiv_initial {r s l : ℕ} (p : Program r s l) (e : Fin s ≃ Fin s)
    (frame : Cfg r s l) (word : List Bool) :
    ProgramLinking.embedCfg id e id none frame (initial p word) =
      initial (ProgramLinking.liftProgram p id e) word := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, initial, extend_equiv]
  funext b
  simp only [e.symm_apply_eq]

theorem lift_equiv_terminal {r s l : ℕ} (p : Program r s l) (e : Fin s ≃ Fin s)
    (frame : Cfg r s l) (word : List Bool) :
    ProgramLinking.embedCfg id e id none frame (terminal p word) =
      terminal (ProgramLinking.liftProgram p id e) word := by
  simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc, terminal, extend_equiv]
  funext b
  simp only [e.symm_apply_eq]

def swapStacks : Equiv.Perm (Fin 3) := Equiv.swap 0 1

abbrev swappedLengthProgram : Program 3 3 14 :=
  ProgramLinking.liftProgram lengthProgram id swapStacks

theorem swappedLength_correct (xs : List Bool) :
    ∃ output, value output = xs.length ∧ output.length ≤ xs.length ∧
      RunsIn swappedLengthProgram (xs.length * (8 * xs.length + 10) + 3)
        (initial swappedLengthProgram xs) (terminal swappedLengthProgram output) := by
  obtain ⟨output, hvalue, hlen, hrun⟩ := length_correct xs
  have h := ProgramLinking.liftProgram_runsIn lengthProgram id swapStacks
    (initial swappedLengthProgram []) Function.injective_id swapStacks.injective hrun
  refine ⟨output, hvalue, hlen, ?_⟩
  simpa only [swappedLengthProgram, lift_equiv_initial, lift_equiv_terminal] using h

abbrev logProgram : Program 3 3 24 := ProgramLinking.link prepareLogProgram swappedLengthProgram

def logBound (L : ℕ) : ℕ := L * (8 * L + 16) + 12

theorem logBound_eq (L : ℕ) : logBound L = 8 * L ^ 2 + 16 * L + 12 := by
  unfold logBound
  ring

theorem logBound_mono {L M : ℕ} (h : L ≤ M) : logBound L ≤ logBound M := by
  exact Nat.add_le_add_right (Nat.mul_le_mul h (by omega : 8 * L + 16 ≤ 8 * M + 16)) 12

/-- Actual fixed-table logarithm program, correct for arbitrary padded words. -/
theorem log_correct (xs : List Bool) :
    ∃ output, value output = Nat.log2 (value xs) ∧ output.length ≤ xs.length ∧
      RunsIn logProgram (logBound xs.length)
        (initial logProgram xs) (terminal logProgram output) := by
  obtain ⟨output, hvalue, hlen, hcount⟩ := swappedLength_correct (trimTail xs.reverse)
  have hrun := link_io_runs prepareLogProgram swappedLengthProgram rfl
    xs (trimTail xs.reverse) output (prepareLog_runs xs) hcount
  have htail : (trimTail xs.reverse).length ≤ xs.length := by
    simpa using trimTail_length_le xs.reverse
  refine ⟨output, hvalue.trans (trimTail_reverse_length xs), hlen.trans htail, hrun.mono ?_⟩
  have hmul := Nat.mul_le_mul htail
    (show 8 * (trimTail xs.reverse).length + 10 ≤ 8 * xs.length + 10 by omega)
  dsimp [logBound]
  nlinarith

/-- Two calls to the same finite logarithm table. -/
abbrev doubleLogProgram : Program 3 3 48 := ProgramLinking.link logProgram logProgram

theorem doubleLog_correct (xs : List Bool) :
    ∃ output, value output = SubexpPackingParameters.s (value xs) ∧
      output.length ≤ xs.length ∧
      RunsIn doubleLogProgram (2 * logBound xs.length)
        (initial doubleLogProgram xs) (terminal doubleLogProgram output) := by
  obtain ⟨middle, hm, hml, hr₁⟩ := log_correct xs
  obtain ⟨output, ho, hol, hr₂⟩ := log_correct middle
  have hr₂' := hr₂.mono (logBound_mono hml)
  have hrun := link_io_runs logProgram logProgram rfl xs middle output hr₁ hr₂'
  refine ⟨output, ?_, hol.trans hml, ?_⟩
  · simpa only [SubexpPackingParameters.s, hm] using ho
  · simpa only [doubleLogProgram, two_mul] using hrun

/-- The entire `n -> s(n) -> u(n)` computation has 55 fixed control labels. -/
abbrev parameterProgram : Program 3 3 55 :=
  ProgramLinking.link doubleLogProgram shiftFourProgram

def parameterBound (L : ℕ) : ℕ := 2 * logBound L + 7

theorem parameterBound_eq (L : ℕ) :
    parameterBound L = 16 * L ^ 2 + 32 * L + 31 := by
  unfold parameterBound logBound
  ring

theorem parameter_correct (xs : List Bool) :
    ∃ output, value output = SubexpPackingParameters.u (value xs) ∧
      output.length ≤ xs.length ∧
      RunsIn parameterProgram (parameterBound xs.length)
        (initial parameterProgram xs) (terminal parameterProgram output) := by
  obtain ⟨middle, hm, hml, hdouble⟩ := doubleLog_correct xs
  have hrun := link_io_runs doubleLogProgram shiftFourProgram rfl xs middle (middle.drop 4)
    hdouble ⟨7, le_rfl, shiftFour_trace middle⟩
  refine ⟨middle.drop 4, ?_, ?_, hrun⟩
  · rw [shiftFour_value, hm]
    rfl
  · simpa only [List.length_drop] using (Nat.sub_le middle.length 4).trans hml

theorem parameter_primitive (xs : List Bool) :
    ∃ output, value output = SubexpPackingParameters.u (value xs) ∧
      output.length ≤ xs.length ∧
      Computation.RunsIn (primitive parameterProgram).step
        (primitiveOverhead parameterProgram * parameterBound xs.length)
        ((primitive parameterProgram).init xs)
        (primitiveCfg parameterProgram (terminal parameterProgram output)) := by
  obtain ⟨output, hv, hl, hr⟩ := parameter_correct xs
  refine ⟨output, hv, hl, ?_⟩
  simpa only [primitive_initial] using BitProgram.primitive_execution parameterProgram hr

end SubexponentialSAT.SubexpParameterProgram

end OAI.Algorithms
