import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Evaluated.ParameterPoints
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.EvaluationDVRLifts

/-! # Evaluation DVR -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting

noncomputable section

/-!
Produce the evaluation DVR directly from a characteristic-zero finite
etale parameter scheme, using the constructed finite splitting field.
-/

universe u

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type u} [Field K] {X : Over (Spec (.of K))}
variable (d : Evaluated.ParameterPoints.Lifts.FiniteEvaluationField K X)
variable (R : Type u) [CommRing R] [Algebra R K]

abbrev Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.scalarAlgebra : Algebra R d.carrier :=
  ((algebraMap K d.carrier).comp (algebraMap R K)).toAlgebra

theorem Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.scalarTower :
    letI := d.scalarAlgebra R
    IsScalarTower R K d.carrier := by
  let := d.scalarAlgebra R
  exact IsScalarTower.of_algebraMap_eq' rfl

variable [CharZero K] [IsDomain R] [IsDiscreteValuationRing R]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable [IsAlgClosed (IsLocalRing.ResidueField R)] [IsFractionRing R K]

/-- This is the complete finite evaluation DVR for the independently
given generic parameter scheme. Henselianity of both DVRs is derived. -/
def Evaluated.ParameterPoints.Lifts.FiniteEvaluationField.integerDVR :
    letI := d.scalarAlgebra R
    EvaluationDVRLifts.EvaluationDVR R d.carrier := by
  letI := d.scalarAlgebra R
  letI := d.scalarTower R
  letI := AdicTransport.Lifts.complete_local_henselian R
  exact EvaluationDVRLifts.evaluationDVR R K d.carrier

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting
