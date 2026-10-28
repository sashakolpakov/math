import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.ModularQuotientLift
import OAI.Algorithms.SubexponentialSAT.ArrayPrograms
import OAI.Algorithms.SubexponentialSAT.SubexpFactorProgram

namespace OAI.Algorithms

/-!
# Actual base-p digit extraction

A digit is obtained by the checked binary long-division program. Its remainder
is copied to the fixed width of the modulus, while the padded high bits are
removed. Repeated extraction uses the quotient as the next rank. The modulus,
arity, and all widths are data; the instruction table is fixed.
-/

namespace SubexponentialSAT.SubexpBasePUnranking

open BitProgram StructuredCalls StackRoutines
open BinaryArithmetic ModularQuotientArithmetic

/-- Fixed-width little-endian digit returned by one division. -/
def digit (modulus rank : List Bool) : List Bool :=
  (divide modulus rank).2.take modulus.length

def nextRank (modulus rank : List Bool) : List Bool := (divide modulus rank).1

@[simp] theorem digit_length (modulus rank : List Bool) :
    (digit modulus rank).length = modulus.length := by
  simp only [digit, List.length_take, divide_remainder_length]
  omega

@[simp] theorem nextRank_length (modulus rank : List Bool) :
    (nextRank modulus rank).length = rank.length := by simp [nextRank]

/-- The discarded high bits are zero when the modulus is positive. Their
removal is therefore justified rather than a truncation approximation. -/
theorem high_bits_zero (modulus rank : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus) :
    BinaryArithmetic.toNat ((divide modulus rank).2.drop modulus.length) = 0 := by
  let low := digit modulus rank
  let high := (divide modulus rank).2.drop modulus.length
  have hsplit : low ++ high = (divide modulus rank).2 :=
    List.take_append_drop _ _
  have hl : low.length = modulus.length := digit_length _ _
  have hlt : BinaryArithmetic.toNat (low ++ high) < 2 ^ low.length := by
    rw [hsplit, hl]
    exact (divide_remainder_lt modulus rank hm).trans (SubexpFactorProgram.toNat_lt_pow_length modulus)
  exact (SubexpFactorProgram.allZero_iff_toNat_zero high).mp
    ((SubexpFactorProgram.unary_validity_iff low high).mpr hlt)

theorem digit_value (modulus rank : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus) :
    BinaryArithmetic.toNat (digit modulus rank) = BinaryArithmetic.toNat rank % BinaryArithmetic.toNat modulus := by
  have hsplit := congrArg BinaryArithmetic.toNat
    (List.take_append_drop modulus.length (divide modulus rank).2)
  rw [SubexpFactorProgram.toNat_append, high_bits_zero modulus rank hm] at hsplit
  calc
    BinaryArithmetic.toNat (digit modulus rank) = BinaryArithmetic.toNat (divide modulus rank).2 := by
      simpa only [digit, Nat.mul_zero, Nat.add_zero] using hsplit
    _ = BinaryArithmetic.toNat rank % BinaryArithmetic.toNat modulus := divide_remainder_correct modulus rank hm

theorem digit_lt (modulus rank : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus) :
    BinaryArithmetic.toNat (digit modulus rank) < BinaryArithmetic.toNat modulus := by
  rw [digit_value modulus rank hm]
  exact Nat.mod_lt _ hm

theorem nextRank_value (modulus rank : List Bool) (hm : 0 < BinaryArithmetic.toNat modulus) :
    BinaryArithmetic.toNat (nextRank modulus rank) = BinaryArithmetic.toNat rank / BinaryArithmetic.toNat modulus :=
  divide_quotient_correct modulus rank hm

/-- Least-significant base-p digit first; each digit itself is little-endian. -/
def digitWords (modulus : List Bool) : ℕ → List Bool → List (List Bool)
  | 0, _ => []
  | k + 1, rank => digit modulus rank :: digitWords modulus k (nextRank modulus rank)

def remainingRank (modulus : List Bool) : ℕ → List Bool → List Bool
  | 0, rank => rank
  | k + 1, rank => remainingRank modulus k (nextRank modulus rank)

@[simp] theorem remainingRank_length (modulus rank : List Bool) (k : ℕ) :
    (remainingRank modulus k rank).length = rank.length := by
  induction k generalizing rank with
  | zero => rfl
  | succ k ih => simpa [remainingRank] using ih (nextRank modulus rank)

@[simp] theorem digitWords_length (modulus rank : List Bool) (k : ℕ) :
    (digitWords modulus k rank).length = k := by
  induction k generalizing rank with
  | zero => rfl
  | succ k ih => simp [digitWords, ih]

@[simp] theorem digitWords_flatten_length (modulus rank : List Bool) (k : ℕ) :
    (digitWords modulus k rank).flatten.length = k * modulus.length := by
  induction k generalizing rank with
  | zero => simp [digitWords]
  | succ k ih => simp [digitWords, ih, Nat.succ_mul, Nat.add_comm]

def numericDigits (p : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k + 1, rank => rank % p :: numericDigits p k (rank / p)

theorem digitWords_values (modulus rank : List Bool) (k : ℕ)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    (digitWords modulus k rank).map BinaryArithmetic.toNat = numericDigits (BinaryArithmetic.toNat modulus) k (BinaryArithmetic.toNat rank) := by
  induction k generalizing rank with
  | zero => rfl
  | succ k ih => simp [digitWords, numericDigits, digit_value modulus rank hm,
      ih, nextRank_value modulus rank hm]

theorem remainingRank_value (modulus rank : List Bool) (k : ℕ)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    BinaryArithmetic.toNat (remainingRank modulus k rank) = BinaryArithmetic.toNat rank / BinaryArithmetic.toNat modulus ^ k := by
  induction k generalizing rank with
  | zero => simp [remainingRank]
  | succ k ih =>
      rw [remainingRank, ih, nextRank_value modulus rank hm, Nat.div_div_eq_div_mul, pow_succ']

theorem remainingRank_zero (modulus rank : List Bool) (k : ℕ)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hrank : BinaryArithmetic.toNat rank < BinaryArithmetic.toNat modulus ^ k) :
    BinaryArithmetic.toNat (remainingRank modulus k rank) = 0 := by
  rw [remainingRank_value modulus rank k hm]
  exact Nat.div_eq_of_lt hrank


/-- Division workspace 0--7; arity counter8; copied width9; transfer scratch10;
reversed digit stream11; final forward digit stream12. -/
def tapes (rem modulus rank quotient arity width scratch rev output : List Bool) :
    Fin 13 → List Bool :=
  fun i => if i = 0 then rem else if i = 5 then modulus else if i = 6 then rank
    else if i = 7 then quotient else if i = 8 then arity else if i = 9 then width
    else if i = 10 then scratch else if i = 11 then rev else if i = 12 then output else []

@[simp] theorem tapes_0 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 0 = rem := rfl
@[simp] theorem tapes_5 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 5 = modulus := rfl
@[simp] theorem tapes_6 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 6 = rank := rfl
@[simp] theorem tapes_7 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 7 = quotient := rfl
@[simp] theorem tapes_8 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 8 = arity := rfl
@[simp] theorem tapes_9 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 9 = width := rfl
@[simp] theorem tapes_10 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 10 = scratch := rfl
@[simp] theorem tapes_11 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 11 = rev := rfl
@[simp] theorem tapes_12 (rem modulus rank quotient arity width scratch rev output : List Bool) :
    tapes rem modulus rank quotient arity width scratch rev output 12 = output := rfl
@[simp] theorem tapes_update_0 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 0 word =
      tapes word modulus rank quotient arity width scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_6 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 6 word =
      tapes rem modulus word quotient arity width scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_7 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 7 word =
      tapes rem modulus rank word arity width scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_8 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 8 word =
      tapes rem modulus rank quotient word width scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_9 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 9 word =
      tapes rem modulus rank quotient arity word scratch rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_10 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 10 word =
      tapes rem modulus rank quotient arity width word rev output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_11 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 11 word =
      tapes rem modulus rank quotient arity width scratch word output := by
  funext j; fin_cases j <;> simp [tapes]
@[simp] theorem tapes_update_12 (rem modulus rank quotient arity width scratch rev output word : List Bool) :
    Function.update (tapes rem modulus rank quotient arity width scratch rev output) 12 word =
      tapes rem modulus rank quotient arity width scratch rev word := by
  funext j; fin_cases j <;> simp [tapes]

def state (regs : Fin 8 → Bool) (modulus rank arity rev output : List Bool) : State 8 13 :=
  ⟨regs, tapes [] modulus rank [] arity [] [] rev output⟩

private theorem copy_eval (src dst tmp : Fin 13)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool) (ht : stk tmp = []) :
    Eval (.call (copyProgram src dst tmp (1 : Fin 8) 3)) (7 * (stk src).length + 5)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, copyStacks src dst stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace src dst tmp (1 : Fin 8) 3 hsd hst htd (by decide) regs stk ht)
    7 rfl rfl
  simpa [StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using h

private theorem clear_eval (src : Fin 13) (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool) :
    Eval (.call (clearProgram src (1 : Fin 8) 3)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, clearStacks src stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _ (clearProgram_trace src (1 : Fin 8) 3 regs stk) 2 rfl rfl
  simpa [StructuredProgram.State.withPC, clearResult, clearProgram, Nat.add_assoc] using h

private theorem transfer_eval (src dst : Fin 13) (hsd : src ≠ dst)
    (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool) :
    Eval (.call (transferProgram src dst (1 : Fin 8) 3)) (3 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs 1 3 none, transferStacks src dst stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (transferProgram_trace src dst (1 : Fin 8) 3 hsd (by decide) regs stk) 3 rfl rfl
  simpa [StructuredProgram.State.withPC, transferResult, transferProgram, Nat.add_assoc] using h

private theorem counted_transfer_eval (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool)
    (low high width : List Bool) (hrem : stk 0 = low ++ high) (hwidth : stk 9 = width)
    (hlen : width.length = low.length) :
    Eval (.call (ArrayPrograms.countedTransferProgram 9 0 11 (1 : Fin 8) 3))
      (4 * low.length + 3) ⟨regs, stk⟩
      ⟨readRegs regs 1 3 none, ArrayPrograms.countedTransferStacks 9 0 11 low high stk⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (ArrayPrograms.countedTransferProgram_trace (9 : Fin 13) 0 11 (1 : Fin 8) 3
      (by decide) (by decide) (by decide) (by decide)
      low high width regs stk hrem hwidth hlen) 4 rfl rfl
  simpa [StructuredProgram.State.withPC, ArrayPrograms.countedTransferResult,
    ArrayPrograms.countedTransferProgram, Nat.add_assoc] using h

/-- Fixed-width digit extraction and quotient preparation after long division.
The digit is prepended in reverse to a stream that is reversed once at the end. -/
abbrev collectDigit : Cmd 8 13 :=
  .seq (.call (copyProgram 5 9 10 1 3))
    (.seq (.call (ArrayPrograms.countedTransferProgram 9 0 11 1 3))
      (.seq (.call (clearProgram 0 1 3))
        (.seq (.call (transferProgram 7 10 1 3)) (.call (transferProgram 10 6 1 3)))))

theorem collectDigit_eval (regs : Fin 8 → Bool)
    (low high modulus quotient arity rev output : List Bool) (hlen : low.length = modulus.length) :
    Eval collectDigit (11 * modulus.length + 2 * high.length + 6 * quotient.length + 17)
      ⟨regs, tapes (low ++ high) modulus [] quotient arity [] [] rev output⟩
      (state (readRegs regs 1 3 none) modulus quotient arity (low.reverse ++ rev) output) := by
  have h₁ := copy_eval 5 9 10 (by decide) (by decide) (by decide) regs
    (tapes (low ++ high) modulus [] quotient arity [] [] rev output) rfl
  simp only [copyStacks, tapes_5, tapes_9, List.append_nil, tapes_update_9] at h₁
  have h₂ := counted_transfer_eval (readRegs regs 1 3 none)
    (tapes (low ++ high) modulus [] quotient arity modulus [] rev output)
    low high modulus rfl rfl hlen.symm
  simp only [ArrayPrograms.countedTransferStacks, tapes_update_9, tapes_update_0,
    tapes_11, tapes_update_11, readRegs_reset] at h₂
  have h₃ := clear_eval 0 (readRegs regs 1 3 none)
    (tapes high modulus [] quotient arity [] [] (low.reverse ++ rev) output)
  simp only [clearStacks, tapes_0, tapes_update_0, readRegs_reset] at h₃
  have h₄ := transfer_eval 7 10 (by decide) (readRegs regs 1 3 none)
    (tapes [] modulus [] quotient arity [] [] (low.reverse ++ rev) output)
  simp only [transferStacks, tapes_7, tapes_10, tapes_update_7, tapes_update_10,
    List.append_nil, readRegs_reset] at h₄
  have h₅ := transfer_eval 10 6 (by decide) (readRegs regs 1 3 none)
    (tapes [] modulus [] [] arity [] quotient.reverse (low.reverse ++ rev) output)
  simp only [transferStacks, tapes_10, tapes_6, tapes_update_10, tapes_update_6,
    List.append_nil, List.reverse_reverse, List.length_reverse, readRegs_reset] at h₅
  have ht := h₁.seq (h₂.seq (h₃.seq (h₄.seq h₅)))
  convert ht using 1
  all_goals first | rfl | omega


def divisionPorts : Fin 8 ↪ Fin 13 where
  toFun i := i.castLE (by decide)
  inj' := by
    intro i j h
    apply Fin.ext
    simpa using congrArg (fun x : Fin 13 => x.val) h

abbrev extractionStep : Cmd 8 13 :=
  .seq (.call (ModularQuotientLift.programAt divisionPorts)) collectDigit

def stepBudget (modulus rank : List Bool) : ℕ :=
  100 * (modulus.length + rank.length + 1) ^ 2 +
    11 * modulus.length + 8 * rank.length + 17

/-- One complete division/extraction step, including actual fixed-width copying
and restoration of the quotient as the next working rank. -/
theorem extractionStep_eval (regs : Fin 8 → Bool)
    (modulus rank arity rev output : List Bool) :
    ∃ n ≤ stepBudget modulus rank, ∃ finalRegs : Fin 8 → Bool,
      Eval extractionStep n (state regs modulus rank arity rev output)
        (state finalRegs modulus (nextRank modulus rank) arity
          ((digit modulus rank).reverse ++ rev) output) := by
  obtain ⟨n, hn, rf, hd⟩ := ModularQuotientLift.programAt_eval divisionPorts modulus rank regs
    (tapes [] modulus rank [] arity [] [] rev output)
    rfl rfl rfl rfl rfl rfl rfl rfl
  change Eval (.call (ModularQuotientLift.programAt divisionPorts)) n
    (state regs modulus rank arity rev output)
    ⟨rf, Function.update (Function.update (Function.update
      (tapes [] modulus rank [] arity [] [] rev output) 0 (divide modulus rank).2)
      6 []) 7 (divide modulus rank).1⟩ at hd
  simp only [tapes_update_0, tapes_update_6, tapes_update_7] at hd
  have hc := collectDigit_eval rf (digit modulus rank)
    ((divide modulus rank).2.drop modulus.length) modulus (nextRank modulus rank)
    arity rev output (digit_length _ _)
  have hsplit : digit modulus rank ++ (divide modulus rank).2.drop modulus.length =
      (divide modulus rank).2 := List.take_append_drop _ _
  rw [hsplit] at hc
  have hhigh : ((divide modulus rank).2.drop modulus.length).length = rank.length := by
    simp only [List.length_drop, divide_remainder_length]
    omega
  have h := hd.seq hc
  refine ⟨_, ?_, readRegs rf 1 3 none, h⟩
  simp only [hhigh, nextRank_length]
  dsimp [stepBudget] at *
  omega

abbrev popArity : Cmd 8 13 := .base (.atom (.pop 8 1 3))

def afterRead (regs : Fin 8 → Bool) (modulus rank arity rev output : List Bool) : State 8 13 :=
  state (readRegs regs 1 3 arity.head?) modulus rank arity.tail rev output

private theorem popArity_eval (regs : Fin 8 → Bool)
    (modulus rank arity rev output : List Bool) :
    Eval popArity 1 (state regs modulus rank arity rev output)
      (afterRead regs modulus rank arity rev output) := by
  have h : (StructuredProgram.Atom.pop (8 : Fin 13) (1 : Fin 8) 3).eval
      (state regs modulus rank arity rev output) =
      afterRead regs modulus rank arity rev output := by
    simp [StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, state, afterRead,
      execInstr]
  rw [← h]
  exact .base (.atom _ _)

abbrev loop : Cmd 8 13 := .while 3 (.seq extractionStep popArity)

/-- The runtime unary arity controls a fixed while loop. Division changes the
rank value but preserves its padded bit width, so each iteration has one common
explicit bound. -/
theorem loop_eval (regs : Fin 8 → Bool) (modulus rank arity rev output : List Bool) :
    ∃ n ≤ arity.length * (stepBudget modulus rank + 2) + 1, ∃ finalRegs : Fin 8 → Bool,
      Eval loop n (afterRead regs modulus rank arity rev output)
        (state finalRegs modulus (remainingRank modulus arity.length rank) []
          ((digitWords modulus arity.length rank).flatten.reverse ++ rev) output) := by
  induction arity generalizing regs rank rev with
  | nil =>
      refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
      have h : (afterRead regs modulus rank [] rev output).regs 3 = false := by
        simp [afterRead, state, readRegs]
      simpa [loop, afterRead, state, remainingRank, digitWords] using
        (Eval.while_false (test := (3 : Fin 8)) (body := .seq extractionStep popArity) h)
  | cons b arity ih =>
      let r₁ := readRegs regs 1 3 (some b)
      obtain ⟨ns, hns, r₂, hs⟩ := extractionStep_eval r₁ modulus rank arity rev output
      have hp := popArity_eval r₂ modulus (nextRank modulus rank) arity
        ((digit modulus rank).reverse ++ rev) output
      obtain ⟨nt, hnt, rf, ht⟩ := ih r₂ (nextRank modulus rank)
        ((digit modulus rank).reverse ++ rev)
      have hb : (afterRead regs modulus rank (b :: arity) rev output).regs 3 = true := by
        simp [afterRead, state, readRegs]
      have hloop := Eval.while_true (test := (3 : Fin 8)) hb (hs.seq hp) ht
      refine ⟨ns + 1 + nt + 1, ?_, rf, ?_⟩
      · have hbudget : stepBudget modulus (nextRank modulus rank) = stepBudget modulus rank := by
          simp [stepBudget]
        rw [hbudget] at hnt
        simp only [List.length_cons, Nat.succ_mul]
        omega
      · simpa [loop, afterRead, r₁, state, List.length_cons, remainingRank, digitWords,
          List.reverse_append, List.append_assoc] using hloop

abbrev command : Cmd 8 13 :=
  .seq popArity (.seq loop (.call (transferProgram 11 12 1 3)))

abbrev program : Program 8 13 (size command + 1) := compiled command 6 12

/-- Explicit cost including all divisions, digit extraction, loop tests, final
stream reversal, and halt. -/
def budget (modulus rank arity : List Bool) : ℕ :=
  arity.length * (100 * (modulus.length + rank.length + 1) ^ 2 +
    14 * modulus.length + 8 * rank.length + 19) + 6

/-- A real execution materializes all fixed-width digit records. The result is
least-significant base-p digit first, with little-endian bits inside each record. -/
theorem command_eval (regs : Fin 8 → Bool) (modulus rank arity output : List Bool) :
    ∃ n, n + 1 ≤ budget modulus rank arity ∧ ∃ finalRegs : Fin 8 → Bool,
      Eval command n (state regs modulus rank arity [] output)
        (state finalRegs modulus (remainingRank modulus arity.length rank) [] []
          ((digitWords modulus arity.length rank).flatten ++ output)) := by
  have hp := popArity_eval regs modulus rank arity [] output
  obtain ⟨nl, hnl, rf, hl⟩ := loop_eval regs modulus rank arity [] output
  simp only [List.append_nil] at hl
  have ht := transfer_eval 11 12 (by decide) rf
    (tapes [] modulus (remainingRank modulus arity.length rank) [] [] [] []
      (digitWords modulus arity.length rank).flatten.reverse output)
  simp only [transferStacks, tapes_11, tapes_12, tapes_update_11, tapes_update_12,
    List.reverse_reverse, List.length_reverse, digitWords_flatten_length] at ht
  have h := hp.seq (hl.seq ht)
  refine ⟨_, ?_, readRegs rf 1 3 none, h⟩
  dsimp [budget, stepBudget] at *
  nlinarith

/-- The checked fixed program implements runtime-arity base-p unranking. -/
theorem program_runsIn (regs : Fin 8 → Bool) (modulus rank arity output : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn program (budget modulus rank arity)
        ((state regs modulus rank arity [] output).withPC (some program.entry))
        ((state finalRegs modulus (remainingRank modulus arity.length rank) [] []
          ((digitWords modulus arity.length rank).flatten ++ output)).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval regs modulus rank arity output
  exact ⟨rf, n + 1, hn, compiled_halt_trace he 6 12⟩

theorem program_primitive (regs : Fin 8 → Bool) (modulus rank arity output : List Bool) :
    ∃ finalRegs : Fin 8 → Bool,
      Computation.RunsIn (BitProgram.primitive program).step
        (BitProgram.primitiveOverhead program * budget modulus rank arity)
        (BitProgram.primitiveCfg program
          ((state regs modulus rank arity [] output).withPC (some program.entry)))
        (BitProgram.primitiveCfg program
          ((state finalRegs modulus (remainingRank modulus arity.length rank) [] []
            ((digitWords modulus arity.length rank).flatten ++ output)).withPC none)) := by
  obtain ⟨rf, hr⟩ := program_runsIn regs modulus rank arity output
  exact ⟨rf, BitProgram.primitive_execution program hr⟩


/-- The same finite table is used for every modulus, rank width, and arity. -/
theorem control_size : size command + 1 = 124 := rfl

theorem digitWords_valid (modulus rank : List Bool) (k : ℕ)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∀ word ∈ digitWords modulus k rank,
      word.length = modulus.length ∧ BinaryArithmetic.toNat word < BinaryArithmetic.toNat modulus := by
  induction k generalizing rank with
  | zero => simp [digitWords]
  | succ k ih =>
      intro word hw
      simp only [digitWords, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact ⟨digit_length _ _, digit_lt _ _ hm⟩
      · exact ih (nextRank modulus rank) word hw

/-- Combined machine-and-value contract for an in-range local table rank.
Every output record has the modulus's fixed bit width and denotes a valid field
label; the quotient after the requested arity has value zero. -/
theorem program_unranks (regs : Fin 8 → Bool) (modulus rank arity output : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) (hrange : BinaryArithmetic.toNat rank < BinaryArithmetic.toNat modulus ^ arity.length) :
    ∃ finalRegs : Fin 8 → Bool,
      RunsIn program (budget modulus rank arity)
        ((state regs modulus rank arity [] output).withPC (some program.entry))
        ((state finalRegs modulus (remainingRank modulus arity.length rank) [] []
          ((digitWords modulus arity.length rank).flatten ++ output)).withPC none) ∧
      BinaryArithmetic.toNat (remainingRank modulus arity.length rank) = 0 ∧
      (digitWords modulus arity.length rank).map BinaryArithmetic.toNat =
        numericDigits (BinaryArithmetic.toNat modulus) arity.length (BinaryArithmetic.toNat rank) ∧
      ∀ word ∈ digitWords modulus arity.length rank,
        word.length = modulus.length ∧ BinaryArithmetic.toNat word < BinaryArithmetic.toNat modulus := by
  obtain ⟨rf, hr⟩ := program_runsIn regs modulus rank arity output
  exact ⟨rf, hr, remainingRank_zero modulus rank arity.length hm hrange,
    digitWords_values modulus rank arity.length hm,
    digitWords_valid modulus rank arity.length hm⟩

end SubexponentialSAT.SubexpBasePUnranking

end OAI.Algorithms
