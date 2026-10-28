import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingScanTriple

namespace OAI.Algorithms

/-! Fixed-control streaming contraction of arbitrary many scalar triples. -/
namespace SubexponentialSAT.SqrtLog.RingScan

open BitProgram StructuredCalls StackRoutines
open SubexponentialSAT.SubexpLiftRing SubexponentialSAT.SubexpQuarticRing

abbrev WordTriple (B : ℕ) := Word B × Word B × Word B

abbrev tripleBits {B : ℕ} : List (WordTriple B) → List Bool
  | [] => []
  | x :: xs => x.1.val ++ (x.2.1.val ++ (x.2.2.val ++ tripleBits xs))

abbrev foldTriples (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t) :
    Word (baseWidth p t) → List (WordTriple (baseWidth p t)) → Word (baseWidth p t)
  | seed, [] => seed
  | seed, x :: xs => foldTriples p t M
      (SubexpPreparedQuartic.wordAdd p t M
        (tripleProduct p t M x.1 x.2.1 x.2.2) seed).1 xs

abbrev tripleLoop : Cmd 8 15 := .while 3 (.seq tripleStep popCount)
abbrev tripleScan : Cmd 8 15 := .seq popCount tripleLoop

private theorem tripleLoop_eval (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width suffix : List Bool)
    (hcount : count.length = triples.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ triples.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 44) + 1,
      ∃ finalRegs, Eval tripleLoop n
        (addState (readRegs regs 1 3 count.head?) M.bits seed.val [] []
          (tripleBits triples ++ suffix) [] count.tail width)
        (addState finalRegs M.bits (foldTriples p t M seed triples).val [] [] suffix [] [] width) := by
  induction triples generalizing seed regs count with
  | nil =>
      have hc : count = [] := List.length_eq_zero_iff.mp (by simpa using hcount)
      subst count
      refine ⟨1, by simp, readRegs regs 1 3 none, ?_⟩
      apply Eval.while_false
      simp [addState, readRegs_present]
  | cons x triples ih =>
      cases count with
      | nil => simp at hcount
      | cons bit count =>
          have hc : count.length = triples.length := by simpa using hcount
          obtain ⟨n, hn, rf, hs⟩ := tripleStep_eval p t M (readRegs regs 1 3 (some bit))
            x.1 x.2.1 x.2.2 seed (tripleBits triples ++ suffix) count width hwidth
          have hp := popCount_eval rf M.bits
            (SubexpPreparedQuartic.wordAdd p t M (tripleProduct p t M x.1 x.2.1 x.2.2) seed).1.val
            [] [] (tripleBits triples ++ suffix) [] count width
          obtain ⟨m, hm, rg, hl⟩ := ih
            (SubexpPreparedQuartic.wordAdd p t M (tripleProduct p t M x.1 x.2.1 x.2.2) seed).1
            rf count hc
          have he := Eval.while_true
            (show (addState (readRegs regs 1 3 (some bit)) M.bits seed.val [] []
              (x.1.val ++ (x.2.1.val ++ (x.2.2.val ++ (tripleBits triples ++ suffix)))) [] count width).regs 3 = true by
                simp [addState, readRegs_present])
            (hs.seq hp) hl
          refine ⟨n + 1 + m + 1, ?_, rg, ?_⟩
          · simp only [List.length_cons]
            nlinarith
          · simpa only [tripleLoop, tripleBits, foldTriples, List.head?_cons, List.tail_cons, List.append_assoc] using he

/-- The streaming controller is fixed. Its input stream and unary count may
have any finite size. Every scalar multiplication/addition and each scan is
included in the bound. -/
theorem tripleScan_eval_suffix (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width suffix : List Bool)
    (hcount : count.length = triples.length) (hwidth : width.length = baseWidth p t) :
    ∃ n ≤ triples.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 44) + 2,
      ∃ finalRegs, Eval tripleScan n
        (addState regs M.bits seed.val [] [] (tripleBits triples ++ suffix) [] count width)
        (addState finalRegs M.bits (foldTriples p t M seed triples).val [] [] suffix [] [] width) := by
  have hp := popCount_eval regs M.bits seed.val [] [] (tripleBits triples ++ suffix) [] count width
  obtain ⟨n, hn, rf, hl⟩ := tripleLoop_eval p t M triples seed regs count width suffix hcount hwidth
  exact ⟨1+n, by omega, rf, hp.seq hl⟩

abbrev tripleScanProgram : Program 8 15 (size tripleScan + 1) := compiled tripleScan 9 0

theorem tripleScanProgram_labels : size tripleScan + 1 = 484 := rfl

theorem tripleScanProgram_run_suffix (p t : ℕ) [Fact p.Prime] (M : SubexpPreparedQuartic.Modulus p t)
    (triples : List (WordTriple (baseWidth p t))) (seed : Word (baseWidth p t))
    (regs : Fin 8 → Bool) (count width suffix : List Bool)
    (hcount : count.length = triples.length) (hwidth : width.length = baseWidth p t) :
    ∃ finalRegs, RunsIn tripleScanProgram
      (triples.length * (18000 * (baseWidth p t + 1)^2 + 48 * baseWidth p t + 44) + 3)
      ((addState regs M.bits seed.val [] [] (tripleBits triples ++ suffix) [] count width).withPC
        (some tripleScanProgram.entry))
      ((addState finalRegs M.bits (foldTriples p t M seed triples).val [] [] suffix [] [] width).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := tripleScan_eval_suffix p t M triples seed regs count width suffix hcount hwidth
  exact ⟨rf, n+1, by omega, compiled_halt_trace he 9 0⟩

end SubexponentialSAT.SqrtLog.RingScan

end OAI.Algorithms
