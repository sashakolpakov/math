import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpRecordScan

namespace OAI.Algorithms

/-! Destructive key comparison with query preservation and complete scratch
cleanup, as a fixed primitive subroutine for dictionary replacement. -/
namespace SubexponentialSAT.SqrtLog.Squarefree.Program
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.SubexpRecordScan

abbrev compareDictionaryKey : Cmd 5 6 :=
  .seq (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
    (.seq (.call compareKeys)
      (.seq (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
        (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1))))

theorem compareDictionaryKey_eval (regs : Fin 5 → Bool)
    (source key query output : List Bool) :
    ∃ n ≤ 11 * key.length + 9 * query.length + 20, ∃ final,
      Eval compareDictionaryKey n
        (recordState regs source key.reverse query.reverse [] [] output)
        (recordState final source [] query.reverse [] [] output) ∧
      final 4 = decide (key = query) := by
  let r0 := readRegs regs 0 1 none
  have hcopy : Eval (.call (StackRoutines.copyProgram 2 3 4 (0 : Fin 5) 1))
      (7 * query.length + 5)
      (recordState regs source key.reverse query.reverse [] [] output)
      (recordState r0 source key.reverse query.reverse query.reverse [] output) := by
    simpa [afterCopy, StackRoutines.copyStacks, recordState, r0] using
      copy_eval (recordState regs source key.reverse query.reverse [] [] output)
        2 3 4 (by decide) (by decide) (by decide) rfl
  obtain ⟨nc, hnc, rr, left, right, hcompare, hanswer, hleft, hright⟩ :=
    compareKeys_eval r0 source key.reverse query.reverse query.reverse [] output
  simp only [List.length_reverse] at hnc hleft hright
  have hans : rr 4 = decide (key = query) := by simpa only [List.reverse_inj] using hanswer
  let r1 := readRegs rr 0 1 none
  let r2 := readRegs r1 0 1 none
  have hclear1 : Eval (.call (StackRoutines.clearProgram 1 (0 : Fin 5) 1))
      (2 * left.length + 3)
      (recordState rr source left query.reverse right [] output)
      (recordState r1 source [] query.reverse right [] output) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, r1] using
      clear_eval (recordState rr source left query.reverse right [] output) 1
  have hclear3 : Eval (.call (StackRoutines.clearProgram 3 (0 : Fin 5) 1))
      (2 * right.length + 3)
      (recordState r1 source [] query.reverse right [] output)
      (recordState r2 source [] query.reverse [] [] output) := by
    simpa [afterClear, StackRoutines.clearStacks, recordState, r2] using
      clear_eval (recordState r1 source [] query.reverse right [] output) 3
  refine ⟨(7 * query.length + 5) + (nc + ((2 * left.length + 3) + (2 * right.length + 3))),
    by omega, r2, hcopy.seq (hcompare.seq (hclear1.seq hclear3)), ?_⟩
  simpa [r2, r1, readRegs] using hans
end SubexponentialSAT.SqrtLog.Squarefree.Program

end OAI.Algorithms
