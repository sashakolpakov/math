import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanAdd

namespace OAI.Algorithms

/-! The vector length is a unary input, never a generated list of instructions. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev popCount : Cmd 8 15 := .base (.atom (.pop 11 1 3))
abbrev addLoop : Cmd 8 15 := .while 3 (.seq addStep popCount)
abbrev addScan : Cmd 8 15 := .seq popCount addLoop

def leftBits {B : ℕ} : List (Word B × Word B) → List Bool
  | [] => []
  | x :: xs => x.1.val ++ leftBits xs

def rightBits {B : ℕ} : List (Word B × Word B) → List Bool
  | [] => []
  | x :: xs => x.2.val ++ rightBits xs

def sumBits (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t) :
    List (Word (baseWidth p t) × Word (baseWidth p t)) → List Bool
  | [] => []
  | x :: xs => (SubexpPreparedQuartic.wordAdd p t M x.1 x.2).1.val ++ sumBits p t M xs

private theorem update_count (modulus left right xs ys out count width next : List Bool) :
    Function.update (addTapes modulus left right xs ys out count width) 11 next =
      addTapes modulus left right xs ys out next width := by
  funext i
  by_cases hi : i = 11
  · subst i; simp [addTapes]
  · simp [addTapes, hi]

theorem popCount_eval (regs : Fin 8 → Bool)
    (modulus left right xs ys out count width : List Bool) :
    Eval popCount 1 (addState regs modulus left right xs ys out count width)
      (addState (readRegs regs 1 3 count.head?) modulus left right xs ys out count.tail width) := by
  apply Eval.base
  convert StructuredProgram.Eval.atom (StructuredProgram.Atom.pop (r := 8) (s := 15) 11 1 3)
    (addState regs modulus left right xs ys out count width) using 1
  cases count <;> simp [ StructuredProgram.Atom.eval, StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr,
    addState,
    addTapes, update_count]

private theorem loop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (out count width : List Bool)
    (hcount : count.length = pairs.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ pairs.length * (6000 * (baseWidth p t + 1)^2 + 31 * baseWidth p t + 29) + 1,
      ∃ finalRegs, Eval addLoop n
        (addState (readRegs regs 1 3 count.head?) M.bits [] []
          (leftBits pairs) (rightBits pairs) out count.tail width)
        (addState finalRegs M.bits [] [] [] [] ((sumBits p t M pairs).reverse ++ out) [] width) := by
  induction pairs generalizing regs out count with
  | nil =>
      have hc : count = [] := List.length_eq_zero_iff.mp (by simpa using hcount)
      subst count
      refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
      apply Eval.while_false
      simp [addState, readRegs_present]
  | cons pair pairs ih =>
      cases count with
      | nil => simp at hcount
      | cons bit count =>
          have hc : count.length = pairs.length := by simpa using hcount
          obtain ⟨n, hn, rf, hs⟩ := addStep_eval p t M (readRegs regs 1 3 (some bit))
            pair.1 pair.2 (leftBits pairs) (rightBits pairs) out count width hwidth
          have hp := popCount_eval rf M.bits [] [] (leftBits pairs) (rightBits pairs)
            ((SubexpPreparedQuartic.wordAdd p t M pair.1 pair.2).1.val.reverse ++ out) count width
          obtain ⟨m, hm, rg, hl⟩ := ih rf
            ((SubexpPreparedQuartic.wordAdd p t M pair.1 pair.2).1.val.reverse ++ out)
            count hc
          have he := Eval.while_true
            (show (addState (readRegs regs 1 3 (some bit)) M.bits [] []
              (leftBits (pair :: pairs)) (rightBits (pair :: pairs)) out count width).regs 3 = true by
                simp [addState, readRegs_present])
            (hs.seq hp) hl
          refine ⟨n + 1 + m + 1, ?_, rg, ?_⟩
          · simp only [List.length_cons]
            nlinarith
          · simpa only [addLoop, leftBits, rightBits, sumBits, List.head?_cons, List.tail_cons,
              List.reverse_append, List.append_assoc] using he

/-- Full vector addition scan. The input counter has one arbitrary bit per
coefficient. Both flat vector suffixes are currently empty; the lower-level
step already permits arbitrary suffixes for embedding in record interpreters. -/
theorem addScan_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (out count width : List Bool)
    (hcount : count.length = pairs.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ pairs.length * (6000 * (baseWidth p t + 1)^2 + 31 * baseWidth p t + 29) + 2,
      ∃ finalRegs, Eval addScan n
        (addState regs M.bits [] [] (leftBits pairs) (rightBits pairs) out count width)
        (addState finalRegs M.bits [] [] [] [] ((sumBits p t M pairs).reverse ++ out) [] width) := by
  have hp := popCount_eval regs M.bits [] [] (leftBits pairs) (rightBits pairs) out count width
  obtain ⟨n, hn, rf, hl⟩ := loop_eval p t M pairs regs out count width hcount hwidth
  exact ⟨1+n, by omega, rf, hp.seq hl⟩


abbrev finishAdd : Cmd 8 15 := .call (transferProgram 10 0 1 3)
abbrev addVector : Cmd 8 15 := .seq addScan finishAdd

private theorem finish_stacks (modulus out width : List Bool) :
    transferStacks (10 : Fin 15) 0 (addTapes modulus [] [] [] [] out [] width) =
      addTapes modulus out.reverse [] [] [] [] [] width := by
  funext i
  by_cases h0 : i = 0
  · subst i; simp [transferStacks, addTapes]
  · by_cases h10 : i = 10
    · subst i; simp [transferStacks, addTapes]
    · simp [transferStacks, addTapes, h0, h10]

theorem finishAdd_eval (regs : Fin 8 → Bool) (modulus out width : List Bool) :
    Eval finishAdd (3 * out.length + 3)
      (addState regs modulus [] [] [] [] out [] width)
      (addState (readRegs regs 1 3 none) modulus out.reverse [] [] [] [] [] width) := by
  have ht := transferProgram_trace (10 : Fin 15) 0 (1 : Fin 8) 3
    (by decide) (by decide) regs (addTapes modulus [] [] [] [] out [] width)
  have hh := halt_after_trace _ ht 3 rfl rfl
  apply Eval.call
  simpa only [addState, StructuredProgram.State.withPC, transferResult, finish_stacks,
    show addTapes modulus [] [] [] [] out [] width 10 = out from rfl,
    Nat.add_assoc] using hh

theorem sumBits_length (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t))) :
    (sumBits p t M pairs).length = pairs.length * baseWidth p t := by
  induction pairs with
  | nil => simp [sumBits]
  | cons pair pairs ih =>
      simp only [sumBits, List.length_append, ih, List.length_cons]
      rw [(SubexpPreparedQuartic.wordAdd p t M pair.1 pair.2).1.property]
      simp [Nat.add_mul, Nat.add_comm]

/-- A complete native flat-vector addition, with forward-order output on
stack zero and empty input/counter/scratch stacks. The width and modulus remain. -/
theorem addVector_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = pairs.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ pairs.length * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 5,
      ∃ finalRegs, Eval addVector n
        (addState regs M.bits [] [] (leftBits pairs) (rightBits pairs) [] count width)
        (addState finalRegs M.bits (sumBits p t M pairs) [] [] [] [] [] width) := by
  obtain ⟨n, hn, rf, hs⟩ := addScan_eval p t M pairs regs [] count width hcount hwidth
  simp only [List.append_nil] at hs
  have hf := finishAdd_eval rf M.bits (sumBits p t M pairs).reverse width
  simp only [List.reverse_reverse, List.length_reverse, sumBits_length] at hf
  refine ⟨_, ?_, readRegs rf 1 3 none, hs.seq hf⟩
  nlinarith

abbrev addVectorProgram : Program 8 15 (size addVector + 1) := compiled addVector 8 0

theorem addVectorProgram_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (pairs : List (Word (baseWidth p t) × Word (baseWidth p t)))
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = pairs.length) (hwidth : width.length = baseWidth p t) :
    ∃ finalRegs, RunsIn addVectorProgram
      (pairs.length * (6000 * (baseWidth p t + 1)^2 + 34 * baseWidth p t + 29) + 6)
      ((addState regs M.bits [] [] (leftBits pairs) (rightBits pairs) [] count width).withPC
        (some addVectorProgram.entry))
      ((addState finalRegs M.bits (sumBits p t M pairs) [] [] [] [] [] width).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := addVector_eval p t M pairs regs count width hcount hwidth
  exact ⟨rf, n + 1, by omega, compiled_halt_trace he 8 0⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
