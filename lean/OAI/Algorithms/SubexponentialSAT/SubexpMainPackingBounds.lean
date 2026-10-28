import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainPacking
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExecutionBounds

namespace OAI.Algorithms

/-!
# Polynomial bound for Main's actual packing invocation

The initial storage term is measured on the projected machine state. It
includes existing export words, so clearing old data remains charged. The
other term bounds the actual packing execution using its original inputs.
-/

namespace SubexponentialSAT.SubexpMainPacking

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation)

variable {U : Type*} [DecidableEq U]

def storageSize {er es : ℕ} (alloc : Allocation es) (a : MainState er es) : ℕ :=
  stackBits ((procedure er alloc).project a).stacks

def polynomialBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (s : PackingExecution.Spec U) : ℕ :=
  30000 * (storageSize alloc a + 81000000 * PackingExecutionBounds.sourceSize s ^ 12 + 1)

theorem runtimeBound_le_polynomial {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (s : PackingExecution.Spec U) :
    runtimeBound alloc a s ≤ polynomialBound alloc a s := by
  have h := PackingExecutionBounds.budget_le s
  unfold runtimeBound Staging.runtimeBound polynomialBound storageSize
  apply Nat.mul_le_mul_left
  exact Nat.add_le_add_right (Nat.add_le_add_left h _) 1

/-- Actual invocation, including staging and cleanup, with a fixed
polynomial in original input sizes and the initially occupied storage. -/
theorem execution_polynomial {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (s : PackingExecution.Spec U) (hi : inputs alloc a = s.params.input) :
    ∃ n ≤ polynomialBound alloc a s, ∃ b,
      Eval (procedure er alloc).invoke n a b ∧ Result alloc a b s := by
  obtain ⟨n, hn, b, he, hr⟩ := execution alloc a s hi
  exact ⟨n, hn.trans (runtimeBound_le_polynomial alloc a s), b, he, hr⟩

theorem program_runsIn_polynomial {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (s : PackingExecution.Spec U)
    (hi : inputs alloc a = s.params.input) :
    ∃ b, RunsIn (program er alloc) (polynomialBound alloc a s)
      (a.withPC (some (program er alloc).entry)) (b.withPC none) ∧ Result alloc a b s := by
  obtain ⟨b, ⟨n, hn, ht⟩, hr⟩ := program_runsIn alloc a s hi
  exact ⟨b, ⟨n, hn.trans (runtimeBound_le_polynomial alloc a s), ht⟩, hr⟩

theorem primitive_runsIn_polynomial {er es : ℕ} (alloc : Allocation es)
    (a : MainState er es) (s : PackingExecution.Spec U)
    (hi : inputs alloc a = s.params.input) :
    ∃ b, Computation.RunsIn (primitive (program er alloc)).step
      (primitiveOverhead (program er alloc) * polynomialBound alloc a s)
      (primitiveCfg (program er alloc) (a.withPC (some (program er alloc).entry)))
      (primitiveCfg (program er alloc) (b.withPC none)) ∧ Result alloc a b s := by
  obtain ⟨b, hb, hr⟩ := program_runsIn_polynomial alloc a s hi
  exact ⟨b, primitive_execution (program er alloc) hb, hr⟩

end SubexponentialSAT.SubexpMainPacking

end OAI.Algorithms
