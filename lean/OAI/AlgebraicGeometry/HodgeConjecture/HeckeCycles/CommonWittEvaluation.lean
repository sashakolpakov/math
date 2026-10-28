import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonFiniteField
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRMap

/-! # Common Witt Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonWittEvaluation.CM

noncomputable section

/-! Construct one finite Witt evaluation DVR containing any two original
finite evaluation fields. Its maps from both original DVRs preserve the
fixed residue identification. -/

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {q : ℕ} [Fact q.Prime]
  (L₁ L₂ : Type) [Field L₁] [Field L₂]
  [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L₁] [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L₂]
  [Module.Finite (Witt.ArithmeticBase.CM.Generic.F q) L₁] [Module.Finite (Witt.ArithmeticBase.CM.Generic.F q) L₂]

abbrev field := CommonFiniteField.CM.commonField (Witt.ArithmeticBase.CM.Generic.F q) L₁ L₂

abbrev scalarAlgebra : Algebra (Witt.ArithmeticBase.CM.W (q := q)) (field (q := q) L₁ L₂).carrier :=
  ((algebraMap (Witt.ArithmeticBase.CM.Generic.F q) (field (q := q) L₁ L₂).carrier).comp (algebraMap (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q))).toAlgebra

theorem scalarTower : letI := scalarAlgebra (q := q) L₁ L₂
    IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) (field (q := q) L₁ L₂).carrier := by
  let := scalarAlgebra (q := q) L₁ L₂
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def valuationDVR : letI := scalarAlgebra (q := q) L₁ L₂
    Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) (field (q := q) L₁ L₂).carrier := by
  letI := scalarAlgebra (q := q) L₁ L₂
  letI := scalarTower (q := q) L₁ L₂
  exact Witt.EvaluationDVR.CM.evaluationDVR q (field (q := q) L₁ L₂).carrier

variable [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L₁] [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L₁]
  [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L₂] [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L₂]
  (V₁ : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L₁) (V₂ : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L₂)

def leftMap : letI := scalarAlgebra (q := q) L₁ L₂
    V₁.carrier →ₐ[Witt.ArithmeticBase.CM.W (q := q)] (valuationDVR (q := q) L₁ L₂).carrier := by
  letI := scalarAlgebra (q := q) L₁ L₂
  letI := scalarTower (q := q) L₁ L₂
  exact EvaluationDVRMap.CM.map V₁ (valuationDVR (q := q) L₁ L₂) (field (q := q) L₁ L₂).left

def rightMap : letI := scalarAlgebra (q := q) L₁ L₂
    V₂.carrier →ₐ[Witt.ArithmeticBase.CM.W (q := q)] (valuationDVR (q := q) L₁ L₂).carrier := by
  letI := scalarAlgebra (q := q) L₁ L₂
  letI := scalarTower (q := q) L₁ L₂
  exact EvaluationDVRMap.CM.map V₂ (valuationDVR (q := q) L₁ L₂) (field (q := q) L₁ L₂).right

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonWittEvaluation.CM
