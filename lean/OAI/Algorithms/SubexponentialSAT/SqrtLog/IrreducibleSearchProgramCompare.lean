import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearchProgramScalar

namespace OAI.Algorithms

/-! Fixed-control equality of equally long serialized coefficient arrays.
Both inputs are consumed. The length premise is supplied by the explicit
coefficient-count invariants, never by an unchecked array access. -/
namespace SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

open SubexponentialSAT.BitProgram

abbrev compareProgram : Program 4 2 8 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.set 3 true 1, .pop 0 0 1 2, .branch 1 3 7,
    .pop 1 2 1 4, .bxor 0 0 2 5, .bnot 0 0 6, .band 3 3 0 1, .halt]

def compareCfg (pc : Option (Fin 8)) (regs : Fin 4 → Bool)
    (left right : List Bool) : Cfg 4 2 8 := ⟨pc, regs, ![left, right]⟩

def compareRoundRegs (regs : Fin 4 → Bool) (a b : Bool) : Fin 4 → Bool :=
  let r := readRegs (readRegs regs 0 1 (some a)) 2 1 (some b)
  let r := Function.update r 0 (!(a ^^ b))
  Function.update r 3 (regs 3 && !(a ^^ b))

theorem compare_round (regs : Fin 4 → Bool) (a b : Bool) (left right : List Bool) :
    Trace compareProgram 6 (compareCfg (some 1) regs (a :: left) (b :: right))
      (compareCfg (some 1) (compareRoundRegs regs a b) left right) := by
  cases a <;> cases b <;> apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, compareProgram, compareCfg,
      compareRoundRegs, execInstr, readRegs, Function.update_apply] <;>
    funext i <;> fin_cases i <;> simp

theorem compare_exit (regs : Fin 4 → Bool) :
    Trace compareProgram 3 (compareCfg (some 1) regs [] [])
      (compareCfg none (readRegs regs 0 1 none) [] []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, compareProgram, compareCfg,
    execInstr, readRegs, Function.update_apply]

theorem compare_loop (left right : List Bool) (hlen : left.length = right.length)
    (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace compareProgram (6 * left.length + 3)
      (compareCfg (some 1) regs left right) (compareCfg none finalRegs [] []) ∧
      finalRegs 3 = (regs 3 && decide (left = right)) := by
  induction left generalizing right regs with
  | nil =>
      have hr : right = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst right
      exact ⟨readRegs regs 0 1 none, compare_exit regs, by simp [readRegs]⟩
  | cons a left ih =>
      cases right with
      | nil => simp at hlen
      | cons b right =>
          obtain ⟨last, ht, hv⟩ := ih right (by simpa using hlen) (compareRoundRegs regs a b)
          refine ⟨last, ?_, ?_⟩
          · have he := (compare_round regs a b left right).trans ht
            convert he using 1 ; simp ; omega
          · cases a <;> cases b <;> simpa [compareRoundRegs, Bool.and_assoc] using hv

theorem compare_run (left right : List Bool) (hlen : left.length = right.length)
    (regs : Fin 4 → Bool) :
    ∃ finalRegs, Trace compareProgram (6 * left.length + 4)
      (compareCfg (some 0) regs left right) (compareCfg none finalRegs [] []) ∧
      finalRegs 3 = decide (left = right) := by
  have hi : Trace compareProgram 1 (compareCfg (some 0) regs left right)
      (compareCfg (some 1) (Function.update regs 3 true) left right) := by
    apply Computation.Trace.of_iterate
    simp [ step, compareProgram, compareCfg, execInstr]
  obtain ⟨last, ht, hv⟩ := compare_loop left right hlen (Function.update regs 3 true)
  refine ⟨last, ?_, by simpa using hv⟩
  have he := hi.trans ht
  simpa only [show 1 + (6 * left.length + 3) = 6 * left.length + 4 by omega] using he

end SubexponentialSAT.SqrtLog.IrreducibleSearchProgram

end OAI.Algorithms
