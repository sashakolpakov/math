import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedLiftProjection

/-! # Lift Recovery -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftRecovery.CM

noncomputable section

/-! Proper specialization of the actual evaluated Witt point recovers
the original prescribed geometric point. Every base square and the
generic projection are supplied by the constructed maps. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ValuativePoints.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PullbackSpecialization.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} {R : M.GoodIntegralReduction q j}
  {hden : Nat.Coprime q M.arithmetic.denominator}
  (X : Over M.arithmetic.base) [IsProper X.hom]
  {p : Geometric.PointExt.CM.pointBase (ArithmeticBase.CM.k (q := q)) ⟶ (Over.pullback R.geometricBase).obj X}
  (l : LiftMap.CM.SmoothPoint.IntegralLift X (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.residueIso (q := q))
    (ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p)
  {L : Type} [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L]
  [Algebra (ArithmeticBase.CM.W (q := q)) L] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L)

local notation "d" => Spec.map (CommRingCat.ofHom (algebraMap ℤ_[q] ℚ_[q]))
local notation "e" => Spec.map (CommRingCat.ofHom (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.localFieldEmbedding j))
local notation "b" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.integralBase j M.arithmetic.denominator hden
local notation "c" => M.arithmetic.generic
local notation "w" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.generic_base_compatible j
  M.arithmetic.denominator M.arithmetic.denominator_ne_zero hden
local notation "bR" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.integralBase V
local notation "cL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.fieldBase (L := L) (q := q)
local notation "wL" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare.CM.generic_square V
local notation "rho" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedReduction.CM.geometricResidue
  (EvaluationDVR.CM.geometricResidueIso V)

omit [IsProper X.hom] in
def evaluatedPoint : ValuativePoints.CM.genericTest (L := L) bR ⟶ PullbackSpecialization.CM.localModel b X :=
  EvaluatedLiftProjection.CM.evaluatedLocalPoint d e b c w X bR cL wL
    (FieldPoint.CM.localTestPoint X l)

theorem specialization_recovers_lift :
    (ValuativePoints.CM.specializePoint bR rho (PullbackSpecialization.CM.localModel b X) (evaluatedPoint X l V)).left ≫
        pullback.fst X.hom b = p.left ≫ pullback.fst X.hom R.geometricBase :=
  EvaluatedLiftProjection.CM.evaluated_specialization_recovers_lift d e b c w X bR cL wL
    (EvaluationDVR.CM.geometricResidueIso V) R.geometricBase p
    (EvaluatedLift.CM.evaluatedLift V hden X l)
    (FieldPoint.CM.localTestPoint X l)
    (FieldPoint.CM.evaluatedLift_projection X l V)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftRecovery.CM
