import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainPackingState
import OAI.Algorithms.SubexponentialSAT.Subexp.PackingExecution

namespace OAI.Algorithms

/-! Actual Main packing execution through the fixed staging wrapper. -/

namespace SubexponentialSAT.SubexpMainPacking

open BitProgram StructuredCalls SubexpMainProgram Subexp
open SubexpLayoutPorts (Allocation)

variable {U : Type*} [DecidableEq U]

def runtimeBound {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (s : PackingExecution.Spec U) : ℕ :=
  Staging.runtimeBound ((procedure er alloc).project a) (PackingExecution.budget s)

/-- All output words follow from the producer's concrete packing execution.
The sole byte equality here identifies its six original input words. -/
theorem execution {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (s : PackingExecution.Spec U) (hi : inputs alloc a = s.params.input) :
    ∃ n ≤ runtimeBound alloc a s, ∃ b,
      Eval (procedure er alloc).invoke n a b ∧ Result alloc a b s := by
  let localStart := (procedure er alloc).project a
  obtain ⟨t, ht, rf, hr⟩ := PackingExecution.program_trace s (Staging.prepared localStart).regs
  have hinput : Staging.inputs localStart = s.params.input := hi
  have hrun : Trace PackingProgram.program t
      ((PackingProgram.inputState (Staging.inputs localStart) (Staging.prepared localStart).regs).withPC
        (some PackingProgram.program.entry)) ((s.outputState rf).withPC none) := by
    simpa only [hinput] using hr
  obtain ⟨n, hn, he⟩ := Staging.run_of_trace localStart (s.outputState rf) ht hrun
  exact ⟨n, hn, (procedure er alloc).install a (Staging.result localStart (s.outputState rf)),
    Procedure.invoke_trace _ _ _ he, install_result alloc a s rf⟩

theorem program_runsIn {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (s : PackingExecution.Spec U) (hi : inputs alloc a = s.params.input) :
    ∃ b, RunsIn (program er alloc) (runtimeBound alloc a s)
      (a.withPC (some (program er alloc).entry)) (b.withPC none) ∧ Result alloc a b s := by
  obtain ⟨n, hn, b, he, hr⟩ := execution alloc a s hi
  refine ⟨b, ⟨n, hn, ?_⟩, hr⟩
  cases he with
  | call _ h => exact h

theorem primitive_runsIn {er es : ℕ} (alloc : Allocation es) (a : MainState er es)
    (s : PackingExecution.Spec U) (hi : inputs alloc a = s.params.input) :
    ∃ b, Computation.RunsIn (primitive (program er alloc)).step
      (primitiveOverhead (program er alloc) * runtimeBound alloc a s)
      (primitiveCfg (program er alloc) (a.withPC (some (program er alloc).entry)))
      (primitiveCfg (program er alloc) (b.withPC none)) ∧ Result alloc a b s := by
  obtain ⟨b, hb, hr⟩ := program_runsIn alloc a s hi
  exact ⟨b, primitive_execution (program er alloc) hb, hr⟩

end SubexponentialSAT.SubexpMainPacking

end OAI.Algorithms
