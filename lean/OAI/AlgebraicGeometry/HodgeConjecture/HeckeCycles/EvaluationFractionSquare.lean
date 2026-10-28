import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints

/-! # Evaluation Fraction Square -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationFractionSquare.CM

noncomputable section

/-! The two actual maps from the finite evaluation field to the Witt
base agree by the scalar towers, including the DVR fraction map. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

variable {q : ℕ} [Fact q.Prime] {L : Type} [Field L]
  [Algebra (Witt.ArithmeticBase.CM.Generic.F q) L] [Algebra (Witt.ArithmeticBase.CM.W (q := q)) L] [IsScalarTower (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (Witt.ArithmeticBase.CM.W (q := q)) L)

theorem fraction_square :
    Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.Generic.F q) L)) ≫ Witt.ArithmeticBase.CM.Generic.fractionBase (q := q) =
      ValuativePoints.CM.genericBase (R := V.carrier) (L := L) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.W (q := q)) V.carrier)) := by
  change Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.Generic.F q) L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q))) =
    Spec.map (CommRingCat.ofHom (algebraMap V.carrier L)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (Witt.ArithmeticBase.CM.W (q := q)) V.carrier))
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext x
  exact (IsScalarTower.algebraMap_apply (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.Generic.F q) L x).symm.trans
    (IsScalarTower.algebraMap_apply (Witt.ArithmeticBase.CM.W (q := q)) V.carrier L x)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationFractionSquare.CM
