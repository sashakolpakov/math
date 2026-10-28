import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.CorrectionVectorProgram

namespace OAI.Algorithms

/-! Terminal execution and exact order of the physical correction vector. -/

namespace SubexponentialSAT.Subexp.CorrectionVectorProgram

open BitProgram StructuredCalls StackRoutines BinaryArithmetic MatrixWordEncoding MulticolorTypes

variable {r Q Δ : ℕ}
variable (p : ℕ) [Fact p.Prime] (i : Fin Δ) (u y : UniversalType r Q Δ)
variable (xs : List (ZMod p))

def loopBound (n : ℕ) : ℕ := n * (coefficientAllowance p i u y xs + 5) + 1

theorem loop_eval (h2 : (2 : ZMod p) ≠ 0) (constant shape : Word)
    (hcw : constant.length = width p) (hcv : BinaryArithmetic.toNat constant = p - 1)
    (hsw : shape.length = 4 * width p)
    (j n : ℕ) (hwithin : j + n ≤ Q) (regs : Fin 10 → Bool) (out : Word)
    (hg : regs 9 = decide (n ≠ 0)) :
    ∃ steps ≤ loopBound p i u y xs n, ∃ rf,
      Eval loop steps (state p i u y xs constant shape regs j n out)
        (state p i u y xs constant shape rf (j + n) 0
          ((vector p i u y xs j n).reverse ++ out)) ∧ rf 9 = false := by
  induction n generalizing j regs out with
  | zero =>
      have hf : regs 9 = false := by simpa using hg
      refine ⟨1, by simp [loopBound], regs, ?_, hf⟩
      simpa [loop, vector] using (Eval.while_false (body := body)
        (a := state p i u y xs constant shape regs j 0 out) hf)
  | succ n ih =>
      have hj : j < Q := by omega
      have hp := pop_eval p i u y xs constant shape regs j n out
      obtain ⟨nc, hnc, rc, hc⟩ := coefficient_eval p i u y xs h2 j n hj constant shape
        (readRegs regs 8 9 (some true)) out hcw hcv hsw
      have ha := advance_eval p i u y xs constant shape rc j n
        ((bytesAt p i u y xs j).reverse ++ out)
      have ht := peek_eval p i u y xs constant shape (Function.update rc 0 true) (j + 1) n
        ((bytesAt p i u y xs j).reverse ++ out)
      obtain ⟨nr, hnr, rr, hr, hrr⟩ := ih (j + 1) (by omega)
        (testedRegs (Function.update rc 0 true) n)
        ((bytesAt p i u y xs j).reverse ++ out) (tested_active _ _)
      have h := Eval.while_true (show
          (state p i u y xs constant shape regs j (n + 1) out).regs 9 = true by
            simpa [state] using hg)
        (hp.seq (hc.seq (ha.seq ht))) hr
      refine ⟨(1 + (nc + (2 + 1))) + nr + 1, ?_, rr, ?_, hrr⟩
      · dsimp [loopBound] at hnr ⊢
        simp only [Nat.add_mul, Nat.one_mul]
        omega
      · convert h using 1
        · rfl
        · apply congrArg (StructuredProgram.State.mk rr)
          funext k
          fin_cases k <;>
            simp [ vector_succ, List.reverse_append, List.append_assoc,
 Nat.add_comm, Nat.add_left_comm]

def input (constant shape : Word) (regs : Fin 10 → Bool) : Data :=
  state p i u y xs constant shape regs 0 0 []

def finished (constant shape : Word) (regs : Fin 10 → Bool) : Data :=
  ⟨regs, Function.update (input p i u y xs constant shape regs).stacks 48
    (vector p i u y xs 0 Q)⟩

def programBudget : ℕ :=
  (7 * Q + 5) + 1 + loopBound p i u y xs Q + (2 * Q + 3) +
    (3 * (Q * (4 * width p)) + 3) + 1

theorem command_eval (h2 : (2 : ZMod p) ≠ 0) (constant shape : Word)
    (hcw : constant.length = width p) (hcv : BinaryArithmetic.toNat constant = p - 1)
    (hsw : shape.length = 4 * width p) (regs : Fin 10 → Bool) :
    ∃ steps, steps + 1 ≤ programBudget p i u y xs ∧ ∃ rf,
      Eval command steps (input p i u y xs constant shape regs)
        (finished p i u y xs constant shape rf) := by
  let a := input p i u y xs constant shape regs
  let rc := readRegs regs 0 1 none
  have hcopy : Eval (.call (copyProgram 22 42 44 (0 : Fin 10) 1)) (7 * Q + 5) a
      (state p i u y xs constant shape rc 0 Q []) := by
    have h := TupleProgram.copy_eval (22 : Fin 49) 42 44 (0 : Fin 10) 1
      (by decide) (by decide) (by decide) (by decide) a
      (by simp +decide [a, input, state])
    convert h using 1
    · simp +decide [a, input, state, MatrixEntryProgram.typedInput, MatrixEntryProgram.input
]
    · apply congrArg (StructuredProgram.State.mk rc)
      funext k
      by_cases hk : k = 42
      · subst k
        simp +decide [copyStacks, a, input, state, MatrixEntryProgram.typedInput, MatrixEntryProgram.input
]
      · simp +decide [copyStacks, a, input, state, hk, Fin.reduceFinMk]
  have hpeek := peek_eval p i u y xs constant shape rc 0 Q []
  obtain ⟨nl, hnl, rl, hl, hrl⟩ := loop_eval p i u y xs h2 constant shape hcw hcv hsw
    0 Q (by omega) (testedRegs rc Q) [] (tested_active _ _)
  simp only [Nat.zero_add, List.append_nil] at hl
  let afterLoop := state p i u y xs constant shape rl Q 0 (vector p i u y xs 0 Q).reverse
  let rd := readRegs rl 0 1 none
  have hclear : Eval (.call (clearProgram 37 (0 : Fin 10) 1)) (2 * Q + 3) afterLoop
      (state p i u y xs constant shape rd 0 0 (vector p i u y xs 0 Q).reverse) := by
    have h := TupleProgram.clear_eval (37 : Fin 49) (0 : Fin 10) 1 afterLoop
    convert h using 1
    · simp +decide [afterLoop, state]
    · apply congrArg (StructuredProgram.State.mk rd)
      funext k
      by_cases hk : k = 37
      · subst k; simp +decide [afterLoop, state, clearStacks]
      · simp +decide [afterLoop, state, clearStacks, hk]
  let beforeTransfer := state p i u y xs constant shape rd 0 0 (vector p i u y xs 0 Q).reverse
  let rf := readRegs rd 0 1 none
  have htransfer : Eval (.call (transferProgram 43 48 (0 : Fin 10) 1))
      (3 * (Q * (4 * width p)) + 3) beforeTransfer (finished p i u y xs constant shape rf) := by
    have h := TupleProgram.transfer_eval (43 : Fin 49) 48 (0 : Fin 10) 1
      (by decide) (by decide) beforeTransfer
    convert h using 1
    · simp +decide [beforeTransfer, state]
    · apply congrArg (StructuredProgram.State.mk rf)
      funext k
      by_cases hk43 : k = 43
      · subst k; simp +decide [ input, beforeTransfer, state, transferStacks]
      · by_cases hk48 : k = 48
        · subst k
          simp +decide [ input, beforeTransfer, state, transferStacks]
        · simp +decide [ input, beforeTransfer, state, transferStacks, hk43, hk48
]
  refine ⟨_, ?_, rf, hcopy.seq (hpeek.seq (hl.seq (hclear.seq htransfer)))⟩
  dsimp [programBudget]
  omega

theorem program_runsIn (h2 : (2 : ZMod p) ≠ 0) (constant shape : Word)
    (hcw : constant.length = width p) (hcv : BinaryArithmetic.toNat constant = p - 1)
    (hsw : shape.length = 4 * width p) (regs : Fin 10 → Bool) :
    ∃ rf, RunsIn program (programBudget p i u y xs)
      ((input p i u y xs constant shape regs).withPC (some program.entry))
      ((finished p i u y xs constant shape rf).withPC none) := by
  obtain ⟨n, hn, rf, he⟩ := command_eval p i u y xs h2 constant shape hcw hcv hsw regs
  exact ⟨rf, n + 1, hn, compiled_halt_trace he 23 48⟩

theorem primitive_runsIn (h2 : (2 : ZMod p) ≠ 0) (constant shape : Word)
    (hcw : constant.length = width p) (hcv : BinaryArithmetic.toNat constant = p - 1)
    (hsw : shape.length = 4 * width p) (regs : Fin 10 → Bool) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * programBudget p i u y xs)
      (BitProgram.primitiveCfg program
        ((input p i u y xs constant shape regs).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((finished p i u y xs constant shape rf).withPC none)) := by
  obtain ⟨rf, ht⟩ := program_runsIn p i u y xs h2 constant shape hcw hcv hsw regs
  exact ⟨rf, BitProgram.primitive_execution _ ht⟩

end SubexponentialSAT.Subexp.CorrectionVectorProgram

end OAI.Algorithms
