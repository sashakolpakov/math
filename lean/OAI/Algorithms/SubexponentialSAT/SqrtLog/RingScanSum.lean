import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanAddLoop

namespace OAI.Algorithms

/-! A native left fold over a flat runtime-sized coefficient stream. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev wordBits {B : ℕ} : List (Word B) → List Bool
  | [] => []
  | x :: xs => x.val ++ wordBits xs

abbrev sumWords (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t) :
    Word (baseWidth p t) → List (Word (baseWidth p t)) → Word (baseWidth p t)
  | seed, [] => seed
  | seed, x :: xs => sumWords p t M (SubexpPreparedQuartic.wordAdd p t M seed x).1 xs

abbrev sumStep : Cmd 8 15 := .seq loadY scalarAdd

theorem sumStep_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (regs : Fin 8 → Bool) (seed x : Word (baseWidth p t))
    (tail count width : List Bool) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ 6000 * (baseWidth p t + 1)^2 + 14 * baseWidth p t + 12,
      ∃ finalRegs, Eval sumStep n
        (addState regs M.bits seed.val [] [] (x.val ++ tail) [] count width)
        (addState finalRegs M.bits (SubexpPreparedQuartic.wordAdd p t M seed x).1.val
          [] [] tail [] count width) := by
  have hl := loadY_eval regs M.bits seed.val x.val tail [] [] count width
    (hwidth.trans x.property.symm)
  obtain ⟨n, hn, rf, ha⟩ := scalarAdd_eval p t M (readRegs regs 1 3 none)
    seed x [] tail [] count width
  refine ⟨_, ?_, rf, hl.seq ha⟩
  simp only [x.property]
  omega

abbrev sumLoop : Cmd 8 15 := .while 3 (.seq sumStep popCount)
abbrev sumVector : Cmd 8 15 := .seq popCount sumLoop

private theorem sumLoop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (words : List (Word (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = words.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ words.length * (6000 * (baseWidth p t + 1)^2 + 14 * baseWidth p t + 14) + 1,
      ∃ finalRegs, Eval sumLoop n
        (addState (readRegs regs 1 3 count.head?) M.bits seed.val [] []
          (wordBits words) [] count.tail width)
        (addState finalRegs M.bits (sumWords p t M seed words).val [] [] [] [] [] width) := by
  induction words generalizing seed regs count with
  | nil =>
      have hc : count = [] := List.length_eq_zero_iff.mp (by simpa using hcount)
      subst count
      refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
      apply Eval.while_false
      simp [addState, readRegs_present]
  | cons x words ih =>
      cases count with
      | nil => simp at hcount
      | cons bit count =>
          have hc : count.length = words.length := by simpa using hcount
          obtain ⟨n, hn, rf, hs⟩ := sumStep_eval p t M (readRegs regs 1 3 (some bit))
            seed x (wordBits words) count width hwidth
          have hp := popCount_eval rf M.bits (SubexpPreparedQuartic.wordAdd p t M seed x).1.val
            [] [] (wordBits words) [] count width
          obtain ⟨m, hm, rg, hl⟩ := ih (SubexpPreparedQuartic.wordAdd p t M seed x).1 rf count hc
          have he := Eval.while_true
            (show (addState (readRegs regs 1 3 (some bit)) M.bits seed.val [] []
              (wordBits (x :: words)) [] count width).regs 3 = true by
                simp [addState, readRegs_present])
            (hs.seq hp) hl
          refine ⟨n + 1 + m + 1, ?_, rg, ?_⟩
          · simp only [List.length_cons]
            nlinarith
          · simpa only [sumLoop, wordBits, sumWords, List.head?_cons, List.tail_cons] using he

/-- The number of scalar summands is supplied solely by the runtime counter.
No summand list is compiled into the program. -/
theorem sumVector_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (words : List (Word (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = words.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ words.length * (6000 * (baseWidth p t + 1)^2 + 14 * baseWidth p t + 14) + 2,
      ∃ finalRegs, Eval sumVector n
        (addState regs M.bits seed.val [] [] (wordBits words) [] count width)
        (addState finalRegs M.bits (sumWords p t M seed words).val [] [] [] [] [] width) := by
  have hp := popCount_eval regs M.bits seed.val [] [] (wordBits words) [] count width
  obtain ⟨n, hn, rf, hl⟩ := sumLoop_eval p t M words seed regs count width hcount hwidth
  exact ⟨1+n, by omega, rf, hp.seq hl⟩

abbrev sumVectorProgram : Program 8 15 (size sumVector + 1) := compiled sumVector 9 0

theorem sumVectorProgram_run (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (words : List (Word (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width : List Bool)
    (hcount : count.length = words.length) (hwidth : width.length = baseWidth p t) :
    ∃ finalRegs, RunsIn sumVectorProgram
      (words.length * (6000 * (baseWidth p t + 1)^2 + 14 * baseWidth p t + 14) + 3)
      ((addState regs M.bits seed.val [] [] (wordBits words) [] count width).withPC
        (some sumVectorProgram.entry))
      ((addState finalRegs M.bits (sumWords p t M seed words).val [] [] [] [] [] width).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := sumVector_eval p t M words seed regs count width hcount hwidth
  exact ⟨rf, n+1, by omega, compiled_halt_trace he 9 0⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
