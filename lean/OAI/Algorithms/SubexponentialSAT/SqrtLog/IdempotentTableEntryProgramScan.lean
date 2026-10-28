import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.StructuredCalls

namespace OAI.Algorithms

/-! A fixed unary scanner. Each complete triple contributes three tokens
to the accumulator; the two output flags encode the remainder modulo three.
No runtime integer arithmetic is an instruction of this machine. -/
namespace SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

open BitProgram StructuredCalls

abbrev scanProgram : Program 4 2 17 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code := ![.pop 0 0 1 1, .branch 1 2 10,
    .pop 0 0 1 3, .branch 1 4 12,
    .pop 0 0 1 5, .branch 1 6 14,
    .set 0 true 7, .push 1 0 8, .push 1 0 9, .push 1 0 0,
    .set 2 false 11, .set 3 false 16,
    .set 2 true 13, .set 3 false 16,
    .set 2 false 15, .set 3 true 16, .halt]

def scanCfg (pc : Option (Fin 17)) (r : Fin 4 → Bool)
    (xs ys : List Bool) : Cfg 4 2 17 := ⟨pc, r, ![xs, ys]⟩

def remainderRegs (n : ℕ) : Fin 4 → Bool :=
  ![false, false, decide (n = 1), decide (n = 2)]

theorem scan_small (r : Fin 4 → Bool) (ys : List Bool) (b : Fin 3) :
    Trace scanProgram (2 * b.val + 5)
      (scanCfg (some 0) r (List.replicate b.val true) ys)
      (scanCfg none (remainderRegs b.val) [] ys) := by
  fin_cases b <;> apply Computation.Trace.of_iterate <;>
    simp [Function.iterate_succ_apply, step, scanProgram, scanCfg, execInstr,
      readRegs, remainderRegs, Function.update_apply]
  all_goals first
    | (constructor <;> (funext i; fin_cases i <;> simp))
    | (funext i; fin_cases i <;> simp)

theorem scan_three (r : Fin 4 → Bool) (xs ys : List Bool) :
    Trace scanProgram 10
      (scanCfg (some 0) r (true :: true :: true :: xs) ys)
      (scanCfg (some 0) (Function.update (Function.update r 0 true) 1 true)
        xs (true :: true :: true :: ys)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, scanProgram, scanCfg, execInstr,
    readRegs, Function.update_apply]
  constructor <;> (funext i; fin_cases i <;> simp)

theorem scan_quotient (q : ℕ) (b : Fin 3) (r : Fin 4 → Bool) (ys : List Bool) :
    Trace scanProgram (10*q + 2*b.val + 5)
      (scanCfg (some 0) r (List.replicate (3*q+b.val) true) ys)
      (scanCfg none (remainderRegs b.val) [] (List.replicate (3*q) true ++ ys)) := by
  induction q generalizing r ys with
  | zero => simpa using scan_small r ys b
  | succ q ih =>
      have h := (scan_three r (List.replicate (3*q+b.val) true) ys).trans
        (ih (Function.update (Function.update r 0 true) 1 true)
          (true :: true :: true :: ys))
      have hn : 3*(q+1)+b.val = 3+(3*q+b.val) := by omega
      have ho : List.replicate (3*q) true ++ true :: true :: true :: ys =
          List.replicate (3*(q+1)) true ++ ys := by
        rw [show 3*(q+1) = 3*q+3 by omega, List.replicate_add]
        simp [List.append_assoc]
      rw [ho] at h
      have hl : List.replicate (3*(q+1)+b.val) true =
          true :: true :: true :: List.replicate (3*q+b.val) true := by
        rw [hn,List.replicate_add]
        rfl
      have hc : 10*(q+1)+2*b.val+5 = 10+(10*q+2*b.val+5) := by omega
      rw [hl,hc]
      exact h

theorem scan_trace (n : ℕ) (r : Fin 4 → Bool) (ys : List Bool) :
    Trace scanProgram (10*(n/3) + 2*(n%3) + 5)
      (scanCfg (some 0) r (List.replicate n true) ys)
      (scanCfg none (remainderRegs (n%3)) []
        (List.replicate (3*(n/3)) true ++ ys)) := by
  have hn : 3*(n/3)+n%3 = n := by omega
  simpa only [hn] using
    scan_quotient (n/3) ⟨n%3, Nat.mod_lt _ (by decide)⟩ r ys

theorem scan_cost (n : ℕ) : 10*(n/3)+2*(n%3)+5 ≤ 4*n+5 := by omega

end SubexponentialSAT.SqrtLog.IdempotentTableEntryProgram

end OAI.Algorithms
