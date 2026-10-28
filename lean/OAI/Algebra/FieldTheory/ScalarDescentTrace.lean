import OAI.Algebra.FieldTheory.ScalarDescentOf
import OAI.Algebra.FieldTheory.TracePairing

/-! # Scalar Descent Trace -/

namespace OAI.Algebra.FieldTheory.ScalarDescentTrace.Core

/-!
# Unconditional ScalarDescent

The original conditional theorem remains available in `ScalarDescent`.
This entrypoint has exactly the original statement's hypotheses and conclusion,
at every universe for the rational space `V`. TracePairing supplies nondegeneracy from
the finite Galois coefficient extension; no result-level input remains.
-/

open scoped TensorProduct

/-- ScalarDescent: scalar-trace descent for a prescribed Hodge bidegree. -/
theorem scalar_trace_descent
    (K : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (V : Type*) [AddCommGroup V] [Module ℚ V]
    (Hpq : Submodule ℂ (AlgebraicGeometry.ComplexMultiplication.WeightOne.CM.Complexification V))
    (t : K ⊗[ℚ] V)
    (hconj : ∀ σ : K ≃ₐ[ℚ] K,
      AlgebraicGeometry.ComplexMultiplication.EmbeddingCoefficientField.CM.coefficientInclusion K V (AlgebraicGeometry.ComplexMultiplication.ScalarDescent.CM.scalarConjugate ℚ K V σ t) ∈ Hpq) :
    t ∈ Submodule.span K
      {y : K ⊗[ℚ] V |
        ∃ v : V,
          y = (1 : K) ⊗ₜ[ℚ] v ∧
          (1 : ℂ) ⊗ₜ[ℚ] v ∈ Hpq} := by
  exact ScalarDescentOf.scalar_trace_descent K V Hpq t hconj
    (TracePairing.HodgeTracePairing.trace_pairing_nondegenerate ℚ K)

end OAI.Algebra.FieldTheory.ScalarDescentTrace.Core
