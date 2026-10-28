import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint.IntrinsicEvaluation
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Parameter.EvaluationDVR
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.ConstructedEvaluation

/-! # Evaluation DVR -/

namespace OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint

noncomputable section

/-! A single complete evaluation DVR serves every native parameter
family and the source torsion. The field, integers, residue comparison,
and finite extension are all constructed. -/

universe u

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {K : Type u} [Field K] {I : Type u}
variable {X : I → Over (Spec (.of K))} (d : IntrinsicEvaluation.Lifts.JointFiniteEvaluationField K X)
variable (R : Type u) [CommRing R] [Algebra R K]

abbrev IntrinsicEvaluation.Lifts.JointFiniteEvaluationField.scalarAlgebra : Algebra R d.carrier :=
  ((algebraMap K d.carrier).comp (algebraMap R K)).toAlgebra

theorem IntrinsicEvaluation.Lifts.JointFiniteEvaluationField.scalarTower :
    letI := d.scalarAlgebra R
    IsScalarTower R K d.carrier := by
  let := d.scalarAlgebra R
  exact IsScalarTower.of_algebraMap_eq' rfl

variable [CharZero K] [IsDomain R] [IsDiscreteValuationRing R]
variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
variable [IsAlgClosed (IsLocalRing.ResidueField R)] [IsFractionRing R K]

def IntrinsicEvaluation.Lifts.JointFiniteEvaluationField.integerDVR :
    letI := d.scalarAlgebra R
    EvaluationDVRLifts.EvaluationDVR R d.carrier := by
  letI := d.scalarAlgebra R
  letI := d.scalarTower R
  letI := AdicTransport.Lifts.complete_local_henselian R
  exact EvaluationDVRLifts.evaluationDVR R K d.carrier

/-- Each independently evaluated family uses this same integer ring. -/
def IntrinsicEvaluation.Lifts.JointFiniteEvaluationField.familyIntegerDVR (i : I) :
    letI : Algebra R (d.family i).carrier := d.scalarAlgebra R
    EvaluationDVRLifts.EvaluationDVR R (d.family i).carrier := d.integerDVR R

end

end OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Joint
