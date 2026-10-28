import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchProgramSupport

namespace OAI.Algorithms

/-! An eight-label comparison of unary counts. Only stack presence is read;
the count values never occur in the finite instruction table. -/

namespace SubexponentialSAT.SqrtLog.CodeSearchProgram

open SubexponentialSAT.BitProgram

abbrev unaryLessProgram : Program 4 2 8 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 5, .pop 1 0 2 3,
    .branch 2 0 4, .set 3 false 7, .peek 1 0 2 6, .copy 3 2 7, .halt]

def unaryLessCfg (pc : Option (Fin 8)) (regs : Fin 4 → Bool)
    (left right : List Bool) : Cfg 4 2 8 := ⟨pc, regs, ![left,right]⟩

theorem unaryLess_nil (regs : Fin 4 → Bool) (right : List Bool) :
    Trace unaryLessProgram 5 (unaryLessCfg (some 0) regs [] right)
      (unaryLessCfg none
        (Function.update (readRegs (readRegs regs 0 1 none) 0 2 right.head?)
          3 right.head?.isSome) [] right) := by
  cases right <;>
    apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, unaryLessProgram, unaryLessCfg,
      execInstr, readRegs, Function.update_apply]

theorem unaryLess_right_nil (regs : Fin 4 → Bool) (a : Bool) (left : List Bool) :
    Trace unaryLessProgram 6 (unaryLessCfg (some 0) regs (a :: left) [])
      (unaryLessCfg none
        (Function.update (readRegs (readRegs regs 0 1 (some a)) 0 2 none) 3 false)
        left []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, unaryLessProgram, unaryLessCfg,
    execInstr, readRegs, Function.update_apply]
  funext i
  fin_cases i <;> simp

theorem unaryLess_round (regs : Fin 4 → Bool) (a b : Bool) (left right : List Bool) :
    Trace unaryLessProgram 4 (unaryLessCfg (some 0) regs (a :: left) (b :: right))
      (unaryLessCfg (some 0) (readRegs (readRegs regs 0 1 (some a)) 0 2 (some b))
        left right) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, unaryLessProgram, unaryLessCfg,
    execInstr, readRegs, Function.update_apply]
  funext i
  fin_cases i <;> simp

theorem unaryLess_trace (left right : List Bool) (regs : Fin 4 → Bool) :
    ∃ n rf l r, n ≤ 4 * left.length + 6 ∧
      Trace unaryLessProgram n (unaryLessCfg (some 0) regs left right)
        (unaryLessCfg none rf l r) ∧
      rf 3 = decide (left.length < right.length) := by
  induction left generalizing right regs with
  | nil =>
      refine ⟨5, _, [], right, by simp, unaryLess_nil regs right, ?_⟩
      cases right <;> simp
  | cons a left ih =>
      cases right with
      | nil =>
          exact ⟨6, _, left, [], by simp, unaryLess_right_nil regs a left, by simp⟩
      | cons b right =>
          obtain ⟨n, rf, l, r, hn, ht, hf⟩ :=
            ih right (readRegs (readRegs regs 0 1 (some a)) 0 2 (some b))
          refine ⟨4 + n, rf, l, r, ?_, (unaryLess_round regs a b left right).trans ht, ?_⟩
          · simp only [List.length_cons]
            omega
          · simpa using hf

theorem unaryLess_runsIn (left right : List Bool) (regs : Fin 4 → Bool) :
    ∃ rf l r, RunsIn unaryLessProgram (4 * left.length + 6)
      (unaryLessCfg (some 0) regs left right) (unaryLessCfg none rf l r) ∧
      rf 3 = decide (left.length < right.length) := by
  obtain ⟨n, rf, l, r, hn, ht, hf⟩ := unaryLess_trace left right regs
  exact ⟨rf, l, r, ⟨n, hn, ht⟩, hf⟩

end SubexponentialSAT.SqrtLog.CodeSearchProgram

end OAI.Algorithms
