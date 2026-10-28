import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.RingProgramTableBasic

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.RingProgramTable

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

/-- Restore forward coefficient order, cache the final coefficient, and append
the vector to the reversed power-table accumulator. -/
abbrev finishVector : Cmd 8 27 :=
  .seq (clear 0) (.seq (transfer 20 15) (.seq (clear 18)
    (.seq (copy 19 18) (.seq (clear 19) (.seq (copy 15 9) (transfer 9 25))))))

theorem finishVector_eval (s : Store) (regs : Fin 8 → Bool)
    (hempty : s.vector = []) (hsource : s.source = []) :
    Eval finishVector
      (2*s.left.length + 13*s.output.length + 2*s.tail.length + 9*s.newTail.length + 25)
      (state regs s)
      (state (readRegs regs 1 3 none) {s with left := [], source := [], vector := s.output.reverse, tail := s.newTail, newTail := [], output := [], powers := s.output ++ s.powers}) := by
  let s1 := {s with left := []}
  let s2 := {s1 with vector := s.output.reverse, output := []}
  let s3 := {s2 with tail := []}
  let s4 := {s3 with tail := s.newTail}
  let s5 := {s4 with newTail := []}
  let s6 := {s5 with source := s.output.reverse}
  let s7 := {s6 with source := [], powers := s.output ++ s.powers}
  let rr := readRegs regs 1 3 none
  have h1 := clear_store_eval s s1 regs 0 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s1])
  have h2 := transfer_store_eval s1 s2 rr 20 15 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s2, s1, hempty])
  have h3 := clear_store_eval s2 s3 rr 18 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s3])
  have h4 := copy_store_eval s3 s4 rr 19 18 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s4, s3, s2, s1])
  have h5 := clear_store_eval s4 s5 rr 19 (by
    funext i; fin_cases i <;> simp [clearStacks, tapes, s5])
  have h6 := copy_store_eval s5 s6 rr 15 9 (by decide) (by decide) (by decide) (by
    funext i; fin_cases i <;> simp [copyStacks, tapes, s6, s5, s4, s3, s2, s1, hsource])
  have h7 := transfer_store_eval s6 s7 rr 9 25 (by decide) (by
    funext i; fin_cases i <;> simp [transferStacks, tapes, s7, s6, s5, s4, s3, s2, s1])
  simp only [rr, readRegs_reset] at h2 h3 h4 h5 h6 h7
  convert h1.seq (h2.seq (h3.seq (h4.seq (h5.seq (h6.seq h7))))) using 1
  simp [s1, s2, s3, s4, s5, s6, tapes]
  omega

end SubexponentialSAT.SqrtLog.RingProgramTable

end OAI.Algorithms
