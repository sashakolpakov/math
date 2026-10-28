import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SubexpMainCoefficients

namespace OAI.Algorithms

/-! The coefficient invocation only needs a word-length bound on the
selected local stacks. Unread Main stacks, including the pending leaf
stream, are framed without any length hypothesis. -/

namespace SubexponentialSAT.SubexpMainCoefficients

open BitProgram StructuredCalls SubexpMainProgram SubexpSetupStorage
open SubexpLayoutPorts

theorem invoke_run_selected {er es : ℕ} (alloc : Allocation es)
    (p r Q R B : ℕ) [Fact p.Prime]
    (hr : 0 < r) (h2 : (2 : ZMod p) ≠ 0) (a : MainState er es)
    (ha : WordBound B ((procedure er alloc).project a))
    (hempty : ∀ i : Fin 64, a.stacks (low alloc i) = [])
    (hpw : CounterPrograms.value (a.stacks (persistent es 6)) = p)
    (hrw : CounterPrograms.value (a.stacks (persistent es 21)) = r)
    (hQw : CounterPrograms.value (a.stacks (persistent es 17)) = Q)
    (hRw : CounterPrograms.value (a.stacks (persistent es 25)) = R) :
    ∃ t b, Eval (procedure er alloc).invoke t a b ∧
      t ≤ SubexpCoefficientProgram.budget p r Q R B ∧
      Nonempty (Result alloc a b p r Q R) := by
  obtain ⟨out, ht, _, hres⟩ := SubexpCoefficientProgram.program_run p r Q R B hr h2
    ((procedure er alloc).project a) ha hpw hrw hQw hRw
  obtain ⟨t, htime, htrace⟩ := ht
  refine ⟨t, (procedure er alloc).install a out,
    (procedure er alloc).invoke_trace a out htrace, htime, ?_⟩
  exact install_result alloc a out p r Q R hempty hres.some

end SubexponentialSAT.SubexpMainCoefficients

end OAI.Algorithms
