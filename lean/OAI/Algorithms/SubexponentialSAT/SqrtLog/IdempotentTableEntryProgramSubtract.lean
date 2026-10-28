import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.IdempotentTableEntryProgramScan

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

/-- Consuming subtraction of unary lengths, with an underflow flag. -/
abbrev subtractProgram : Program 4 2 7 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 4, .pop 1 0 2 3,
    .branch 2 0 5, .set 3 false 6, .set 3 true 6, .halt]

def subCfg (pc : Option (Fin 7)) (r : Fin 4 → Bool)
    (xs ys : List Bool) : Cfg 4 2 7 := ⟨pc, r, ![xs, ys]⟩

theorem sub_nil (r : Fin 4 → Bool) (ys : List Bool) :
    Trace subtractProgram 4 (subCfg (some 0) r [] ys)
      (subCfg none (Function.update (readRegs r 0 1 none) 3 false) [] ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, subCfg,
    execInstr, readRegs, Function.update_apply]

theorem sub_fail (r : Fin 4 → Bool) (xs : List Bool) :
    Trace subtractProgram 6 (subCfg (some 0) r (true :: xs) [])
      (subCfg none
        (Function.update (readRegs (readRegs r 0 1 (some true)) 0 2 none) 3 true)
        xs []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, subCfg,
    execInstr, readRegs, Function.update_apply]
  all_goals
    funext i
    fin_cases i <;> simp

theorem sub_round (r : Fin 4 → Bool) (xs ys : List Bool) :
    Trace subtractProgram 4 (subCfg (some 0) r (true :: xs) (true :: ys))
      (subCfg (some 0) (readRegs (readRegs r 0 1 (some true)) 0 2 (some true))
        xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, subtractProgram, subCfg,
    execInstr, readRegs, Function.update_apply]
  all_goals
    funext i
    fin_cases i <;> simp

theorem subtract_trace (a b : ℕ) (r : Fin 4 → Bool) :
    ∃ n rf xs, n ≤ 4*a+4 ∧
      Trace subtractProgram n
        (subCfg (some 0) r (List.replicate a true) (List.replicate b true))
        (subCfg none rf xs (List.replicate (b-a) true)) ∧
      rf 3 = decide (b < a) ∧ xs.length ≤ a := by
  induction a generalizing b r with
  | zero =>
      exact ⟨4, _, [], by omega, sub_nil r _, by simp, by simp⟩
  | succ a ih =>
      cases b with
      | zero =>
          refine ⟨6,Function.update (readRegs (readRegs r 0 1 (some true)) 0 2 none) 3 true,
            List.replicate a true,by omega,?_,by simp,by simp⟩
          simpa only [List.replicate_succ,List.replicate_zero,Nat.zero_sub] using
            sub_fail r (List.replicate a true)
      | succ b =>
          obtain ⟨n, rf, xs, hn, hrun, hf, hx⟩ :=
            ih b (readRegs (readRegs r 0 1 (some true)) 0 2 (some true))
          refine ⟨4+n,rf,xs,by omega,?_,by simpa using hf,by omega⟩
          simpa only [List.replicate_succ,Nat.add_sub_add_right] using
            (sub_round r (List.replicate a true) (List.replicate b true)).trans hrun

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
