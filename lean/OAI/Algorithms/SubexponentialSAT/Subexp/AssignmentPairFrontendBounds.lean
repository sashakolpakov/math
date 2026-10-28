import OAI.Algorithms.SubexponentialSAT.LeanCompat
import OAI.Algorithms.SubexponentialSAT.Subexp.AssignmentPairFrontend
import OAI.Algorithms.SubexponentialSAT.SubexpVertexPairComplexity

namespace OAI.Algorithms

/-! Explicit polynomial cost for the physical assignment pair frontend. -/

namespace SubexponentialSAT.Subexp.AssignmentPairFrontend

open BitProgram StructuredCalls

def polynomialBudget (D Δ : ℕ) (scopes : List (List ℕ)) : ℕ :=
  60 * (SubexpVertexPairProgram.polynomialBound D Δ scopes +
    (SubexpPlanAlphabetBase.scopeBytes scopes).length + 4)

theorem sourceBudget_le_polynomial (D Δ : ℕ) (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    sourceBudget D Δ scopes ≤ polynomialBudget D Δ scopes := by
  have h := SubexpVertexPairProgram.bound_le_polynomial D Δ scopes hd
  unfold sourceBudget polynomialBudget
  omega

theorem primitive_run_polynomial (regs : Fin 16 → Bool) (r Q Δ D : ℕ)
    (scopes : List (List ℕ))
    (hd : ∀ v : Fin D, IncidencePlanSpec.degree scopes v.val ≤ Δ) :
    ∃ rf, Computation.RunsIn (BitProgram.primitive program).step
      (BitProgram.primitiveOverhead program * polynomialBudget D Δ scopes)
      (BitProgram.primitiveCfg program
        ((inputState regs r Q Δ D scopes).withPC (some program.entry)))
      (BitProgram.primitiveCfg program
        ((AssignmentInputProgram.inputState rf r Q Δ D scopes.length
          (pairBytes D Δ scopes)).withPC none)) := by
  obtain ⟨rf, n, hn, ht⟩ := program_run regs r Q Δ D scopes hd
  exact ⟨rf, BitProgram.primitive_execution program
    ⟨n, hn.trans (sourceBudget_le_polynomial D Δ scopes hd), ht⟩⟩

end SubexponentialSAT.Subexp.AssignmentPairFrontend

end OAI.Algorithms
