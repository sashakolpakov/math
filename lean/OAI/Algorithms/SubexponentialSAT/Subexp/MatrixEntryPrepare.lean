import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.MatrixEntryFrames

namespace OAI.Algorithms

/-! Actual preparation of the coefficient workspace from the two scan counts.
The first count is positive: its first token is the distinguished joint
coordinate. All remaining operations are concrete copies, transfers and pushes. -/

namespace SubexponentialSAT.Subexp.MatrixEntryProgram

open BitProgram StructuredCalls StackRoutines

def counted (base : Data) (regs : Fin 9 → Bool) (A B : ℕ) : Data :=
  ⟨regs, fun j =>
    if j = 2 then List.replicate A true
    else if j = 3 then List.replicate B true
    else if j = 22 then []
    else if j = 33 then base.stacks 22
    else if j = 34 ∨ j = 35 ∨ j = 36 then []
    else base.stacks j⟩

def prepared (base : Data) (regs : Fin 9 → Bool) (A B : ℕ) : Data :=
  ⟨regs, fun j =>
    if h : j.val < 18 then
      (MatrixPaddingProgram.state (fun i => regs (lowRegisters i))
        (base.stacks 31) (base.stacks 30) (base.stacks 29)
        (true :: base.stacks 22) (base.stacks 32)).stacks ⟨j.val, h⟩
    else if j = 22 then []
    else if j = 33 then base.stacks 22
    else if j = 34 ∨ j = 35 then List.replicate A true
    else if j = 36 then List.replicate B true
    else base.stacks j⟩

def prepareCost (base : Data) (A B : ℕ) : ℕ :=
  1 + (6 * A + 6) + (7 * A + 5) + (6 * B + 6) +
    (7 * (base.stacks 22).length + 5) + 2 +
    (7 * (base.stacks 29).length + 5) + (7 * (base.stacks 30).length + 5) +
    (7 * (base.stacks 31).length + 5) + (7 * (base.stacks 32).length + 5)

theorem prepare_eval (base : Data) (regs : Fin 9 → Bool) (A B : ℕ)
    (hclear : ∀ j : Fin 37, j.val < 21 → base.stacks j = []) :
    ∃ out, Eval prepare (prepareCost base A B)
      (counted base regs (A + 1) B) (prepared base out A B) := by
  have h9 : base.stacks 9 = [] := hclear 9 (by decide)
  let a := counted base regs (A + 1) B
  let a1 := popped a 2
  let a2 := moved a1 2 35
  let a3 := copied a2 35 34
  let a4 := moved a3 3 36
  let a5 := copied a4 33 16
  let a6 := pushed a5 16
  let a7 := copied a6 29 5
  let a8 := copied a7 30 14
  let a9 := copied a8 31 12
  let a10 := copied a9 32 17
  have t0 := pop_eval a 2
  have t1 := move_eval a1 2 35 (by decide) (by decide)
    (by simpa [a1, a, popped, counted] using hclear 9 (by decide))
  have t2 := copy_eval a2 35 34 (by decide) (by decide) (by decide)
    (by simp [a2, moved, transferred, transferStacks])
  have t3 := move_eval a3 3 36 (by decide) (by decide)
    (by simp [a3, a2, copied, moved, transferred, transferStacks, copyStacks])
  have t4 := copy_eval a4 33 16 (by decide) (by decide) (by decide)
    (by simp [a4, moved, transferred, transferStacks])
  have t5 := push_eval a5 16
  have t6 := copy_eval a6 29 5 (by decide) (by decide) (by decide)
    (by simp [a6, a5, a4, pushed, TupleProgram.pushedState, copied, copyStacks,
      moved, transferred, transferStacks])
  have t7 := copy_eval a7 30 14 (by decide) (by decide) (by decide)
    (by simp [a7, a6, a5, a4, copied, copyStacks, pushed, TupleProgram.pushedState,
      moved, transferred, transferStacks])
  have t8 := copy_eval a8 31 12 (by decide) (by decide) (by decide)
    (by simp [a8, a7, a6, a5, a4, copied, copyStacks, pushed, TupleProgram.pushedState,
      moved, transferred, transferStacks])
  have t9 := copy_eval a9 32 17 (by decide) (by decide) (by decide)
    (by simp [a9, a8, a7, a6, a5, a4, copied, copyStacks, pushed, TupleProgram.pushedState,
      moved, transferred, transferStacks])
  have hf : a10 = prepared base a10.regs A B := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;>
        simp +decide [a10, a9, a8, a7, a6, a5, a4, a3, a2, a1, a,
 counted, copied, moved, transferred, popped, pushed,
          TupleProgram.pushedState, transferStacks, copyStacks,
          MatrixPaddingProgram.state, hclear, List.replicate_succ]
  have he := t0.seq (t1.seq (t2.seq (t3.seq (t4.seq (t5.seq (t6.seq
    (t7.seq (t8.seq (t9.seq (Eval.base (StructuredProgram.Eval.skip a10)))))))))))
  rw [hf] at he
  refine ⟨a10.regs, ?_⟩
  convert he using 1 <;> first
    | rfl
    | omega
    | (simp [prepareCost, a, a1, a2, a3, a4, a5, a6, a7, a8, a9,
        counted, popped, moved, transferred, copied, pushed, TupleProgram.pushedState,
        transferStacks, copyStacks, hclear, List.replicate_succ] ; omega)

theorem prepared_projection (base : Data) (regs : Fin 9 → Bool) (A B : ℕ) :
    project (by decide : 18 ≤ 37) (prepared base regs A B) =
      MatrixPaddingProgram.state (fun i => regs (lowRegisters i))
        (base.stacks 31) (base.stacks 30) (base.stacks 29)
        (true :: base.stacks 22) (base.stacks 32) := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    simp [ prepared, j.isLt]
    rfl

end SubexponentialSAT.Subexp.MatrixEntryProgram

end OAI.Algorithms
