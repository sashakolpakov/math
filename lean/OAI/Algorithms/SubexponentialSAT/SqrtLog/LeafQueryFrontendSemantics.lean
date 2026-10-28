import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafQueryFrontendCore
import OAI.Algorithms.SubexponentialSAT.SqrtLog.CostAssemblyProducedGuards

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafQueryFrontend
open SubexponentialSAT BitProgram StructuredCalls

@[simp] theorem Query.forward_length (q : Query) :
    q.forward.length=BinaryArithmetic.toNat q.ambient := by
  simp [Query.forward,highMask]

/-- The physically loaded parameter input is exactly the neutral-completed
statistics input used by the uniform guard theorem. -/
theorem Query.input_eq_measured (q : Query) (k : ℕ)
    (hm : BinaryArithmetic.toNat q.modulus=q.clauses.length) :
    q.input k=CostAssembly.measuredParameterInput q.scopeRows q.forward q.clauses.length k := by
  unfold Query.input numericInput CostAssembly.measuredParameterInput
  simp only [Query.forward_length,hm]
  rfl

theorem query_guard_cutoff (C exponent : ℕ) :
    ∃ N : ℕ, ∀ (q : Query) (k : ℕ),
      N ≤ BinaryArithmetic.toNat q.ambient →
      BinaryArithmetic.toNat q.modulus=q.clauses.length →
      BinaryArithmetic.toNat q.ambient ≤ 2*(LeafStatisticsProgram.measured q.scopeRows q.forward).free →
      0 < q.clauses.length → (∀ row ∈ q.scopeRows,row.Nodup) →
      (LeafStatisticsProgram.measured q.scopeRows q.forward).occurrence ≤
        C*Asymptotic.L (BinaryArithmetic.toNat q.ambient)^exponent →
      CostAssembly.measuredArity q.scopeRows q.forward ≤
        C*Asymptotic.L (BinaryArithmetic.toNat q.ambient)^exponent →
      LeafParametersProgram.Guard (q.input k) := by
  obtain ⟨N,hN⟩ := CostAssembly.measured_guards_uniform_cutoff C exponent
  refine ⟨N,?_⟩
  intro q k hn hm hhalf hc hnodup hB ha
  rw [q.input_eq_measured k hm]
  exact (hN _ hn q.scopeRows q.forward q.clauses.length k q.forward_length hhalf hc hnodup hB ha).1

end SubexponentialSAT.SqrtLog.LeafQueryFrontend

end OAI.Algorithms
