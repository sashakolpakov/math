import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.MatchedLevelExtraction
import OAI.AlgebraicGeometry.HodgeConjecture.CMExtraction.SameTestProjector
import OAI.Algebra.FieldTheory.ScalarDescentOf
import OAI.Algebra.FieldTheory.TracePairing

/-! # Established CM Extraction -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedCMExtraction.CM

noncomputable section

/-! Discharge the complete original CMExtraction input.

The scalar-trace premise of the proved CMExtraction implication follows from the
trace-dual basis of the finite separable coefficient field. All five CMExtraction
conclusions are retained. No trace-descent or extraction claim is assumed.
-/

open scoped TensorProduct

universe uV uI uPhi uB

theorem scalar_trace (K : IntermediateField ℚ ℂ) [NumberField K] [IsGalois ℚ K]
    (W : Type*) [AddCommGroup W] [Module ℚ W] :
    CMExtraction.SameTestProjector.ScalarTraceInput K W := by
  intro Hpq t hconj
  exact Algebra.FieldTheory.ScalarDescentOf.scalar_trace_descent K W Hpq t hconj
    (Algebra.FieldTheory.TracePairing.HodgeTracePairing.trace_pairing_nondegenerate ℚ K)

theorem full_input : MatchedLevelExtraction.CM.Construction.CMExtractionInput := by
  intro E K _ _ _ _ _ v hv hK res hres V _ _ H
  exact CMExtraction.SameTestProjector.cm_extraction_from_galois_conjugate_hodge_signs
    E K v hv hK res hres V H (scalar_trace K (E →ₗ[ℚ] V))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EstablishedCMExtraction.CM
