import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.PaddedCompletion
import OAI.Algorithms.SubexponentialSAT.Subexp.UnaryCompare

namespace OAI.Algorithms

/-!
# A fixed bit program tallying padded collision leaves

Each successful leaf pushes one false bit. The resulting unary stack is the
exact common numerator used for conditional expectation. This file proves the
actual instruction trace from a prepared Boolean leaf list.
-/

namespace SubexponentialSAT.Subexp.UnaryTally

open SubexponentialSAT.BitProgram SubexponentialSAT.Subexp.PaddedCompletion

abbrev program : Program 2 2 6 where
  inputStack := 0
  outputStack := 1
  entry := 0
  code q := match q.val with
    | 0 => .pop 0 0 1 1
    | 1 => .branch 1 2 5
    | 2 => .branch 0 3 0
    | 3 => .set 0 false 4
    | 4 => .push 1 0 0
    | _ => .halt

def pairStacks (xs out : List Bool) : Fin 2 → List Bool :=
  fun i => if i = 0 then xs else out

def start (regs : Fin 2 → Bool) (xs out : List Bool) : Cfg 2 2 6 :=
  ⟨some 0, regs, pairStacks xs out⟩

def finish (out : List Bool) : Cfg 2 2 6 :=
  ⟨none, fun _ => false, pairStacks [] out⟩

def loopRegs : Fin 2 → Bool := fun i => decide (i = 1)

def steps : List Bool → ℕ
  | [] => 3
  | b :: xs => (if b then 5 else 3) + steps xs

private theorem trueCount_nil : trueCount [] = 0 := rfl
private theorem trueCount_false (xs : List Bool) : trueCount (false :: xs) = trueCount xs := rfl
private theorem trueCount_true (xs : List Bool) : trueCount (true :: xs) = trueCount xs + 1 := rfl

private theorem replicate_append_bit (n : ℕ) (out : List Bool) :
    List.replicate n false ++ false :: out = List.replicate (n + 1) false ++ out := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons false) ih

theorem nil_trace (regs : Fin 2 → Bool) (out : List Bool) :
    Trace program 3 (start regs [] out) (finish out) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, finish, readRegs, pairStacks]
  funext i
  fin_cases i <;> simp

theorem false_trace (regs : Fin 2 → Bool) (xs out : List Bool) :
    Trace program 3 (start regs (false :: xs) out) (start loopRegs xs out) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, readRegs, pairStacks ]
  constructor
  · funext i
    fin_cases i <;> simp [loopRegs]
  · funext i
    fin_cases i <;> simp [pairStacks]

theorem true_trace (regs : Fin 2 → Bool) (xs out : List Bool) :
    Trace program 5 (start regs (true :: xs) out) (start loopRegs xs (false :: out)) := by
  apply SubexponentialSAT.Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr,
    start, readRegs, pairStacks ]
  constructor
  · funext i
    fin_cases i <;> simp [loopRegs]
  · funext i
    fin_cases i <;> simp [pairStacks]

/-- Exact instruction trace, including the final halt. -/
theorem tally_trace (regs : Fin 2 → Bool) (xs out : List Bool) :
    Trace program (steps xs) (start regs xs out)
      (finish (List.replicate (trueCount xs) false ++ out)) := by
  induction xs generalizing regs out with
  | nil => simpa only [steps, trueCount_nil, List.replicate_zero, List.nil_append] using nil_trace regs out
  | cons b xs ih =>
      cases b with
      | false =>
          simpa only [steps, Bool.false_eq_true, ↓reduceIte, trueCount_false] using
            (false_trace regs xs out).trans (ih loopRegs out)
      | true =>
          simpa only [steps, ↓reduceIte, trueCount_true, replicate_append_bit] using
            (true_trace regs xs out).trans (ih loopRegs (false :: out))

theorem steps_eq (xs : List Bool) : steps xs = 3 * xs.length + 2 * trueCount xs + 3 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b <;> simp only [steps, trueCount_false, trueCount_true, List.length_cons, ih,
        Bool.false_eq_true, ↓reduceIte] <;> omega

theorem steps_le (xs : List Bool) : steps xs ≤ 5 * xs.length + 3 := by
  have h : trueCount xs ≤ xs.length := List.length_filter_le id xs
  rw [steps_eq]
  omega

theorem tally_runsIn (regs : Fin 2 → Bool) (xs out : List Bool) :
    RunsIn program (5 * xs.length + 3) (start regs xs out)
      (finish (List.replicate (trueCount xs) false ++ out)) :=
  ⟨steps xs, steps_le xs, tally_trace regs xs out⟩

theorem tally_primitive_runsIn (regs : Fin 2 → Bool) (xs out : List Bool) :
    SubexponentialSAT.Computation.RunsIn (primitive program).step
      (primitiveOverhead program * (5 * xs.length + 3))
      (primitiveCfg program (start regs xs out))
      (primitiveCfg program (finish (List.replicate (trueCount xs) false ++ out))) :=
  primitive_execution program (tally_runsIn regs xs out)

section Scores

open SubexponentialSAT.MulticolorTypes SubexponentialSAT.SubexpTypeVariance SubexponentialSAT.SlotAssignment
open SubexponentialSAT.Subexp.LocalExpectation

variable {V E : Type*} [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable (P : SubexponentialSAT.Factor.Pattern V E) {r Q Δ : ℕ} [NeZero r] (slots : SlotMap P Δ)

omit [Fintype V] [NeZero r] in
/-- Padded completion leaves are tallied by this fixed program into the exact
unary numerator expected by UnaryCompare. -/
theorem pairNumerator_runsIn (alphabet : List (Word r Q))
    (haNodup : alphabet.Nodup) (haFull : ∀ w, w ∈ alphabet)
    (vertices : List V) (remaining : List (SeedIndex V E Δ)) (hr : remaining.Nodup)
    (ω : Assignment V E r Q Δ) (regs : Fin 2 → Bool) :
    RunsIn program (5 * (vertices.length ^ 2 * (blockSize r Q Δ) ^ 2) + 3)
      (start regs (pairLeaves P slots alphabet vertices remaining ω) [])
      (finish (UnaryCompare.encode (pairNumerator P slots alphabet vertices remaining ω))) := by
  simpa only [pairLeaves_length_eq_block P slots alphabet haNodup haFull vertices remaining hr ω,
    pairLeaves_trueCount, List.append_nil, UnaryCompare.encode] using
    tally_runsIn regs (pairLeaves P slots alphabet vertices remaining ω) []

end Scores

end SubexponentialSAT.Subexp.UnaryTally

end OAI.Algorithms
