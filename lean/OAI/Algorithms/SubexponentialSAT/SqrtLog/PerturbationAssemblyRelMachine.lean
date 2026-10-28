import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.PerturbationAssemblyProgram

namespace OAI.Algorithms

/-! Compile an individual relational execution of the closed producer. This
bridge retains the actual output witness instead of quantifying it before
all possible initial register files. -/
namespace SubexponentialSAT.SqrtLog.PerturbationAssembly
open SubexponentialSAT BitProgram StructuredCalls

theorem program_run_of_eval (s out : OuterData) (k K : ℕ)
    (h : Eval command k s out) (hk : k ≤ K) :
    RunsIn program (K+1) (s.withPC (some program.entry)) (out.withPC none) := by
  exact ⟨k+1,Nat.add_le_add_right hk 1,compiled_halt_trace h 556 561⟩

theorem program_primitive_of_eval (s out : OuterData) (k K : ℕ)
    (h : Eval command k s out) (hk : k ≤ K) :
    Computation.RunsIn (primitive program).step (primitiveOverhead program*(K+1))
      (primitiveCfg program (s.withPC (some program.entry)))
      (primitiveCfg program (out.withPC none)) :=
  primitive_execution program (program_run_of_eval s out k K h hk)

end SubexponentialSAT.SqrtLog.PerturbationAssembly

end OAI.Algorithms
