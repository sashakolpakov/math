import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SameTestProjector
import OAI.Algebra.FieldTheory.ScalarDescentOf
import OAI.Algebra.FieldTheory.TracePairing

/-! # Scalar Trace -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarTrace

noncomputable section

/-! The scalar-trace input in the unchanged extraction theorem follows
from the proved ScalarDescent and the nondegenerate number-field trace pairing. -/

theorem scalarTraceInput_of_numberField
    (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
    (V : Type*) [AddCommGroup V] [Module ℚ V] : SameTestProjector.ScalarTraceInput K V := by
  intro Hpq t hconj
  exact Algebra.FieldTheory.ScalarDescentOf.scalar_trace_descent K V Hpq t hconj
    (Algebra.FieldTheory.TracePairing.HodgeTracePairing.trace_pairing_nondegenerate ℚ K)

end

end OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.ScalarTrace
