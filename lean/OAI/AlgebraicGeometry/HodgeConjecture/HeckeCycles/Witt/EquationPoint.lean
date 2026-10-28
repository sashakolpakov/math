import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ArithmeticEquationPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftRecovery
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.PointFrobenius

/-! # Equation Point -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EquationPoint.CM

noncomputable section

/-! The point appearing in the transported source equation, when
constructed from the actual Witt lift, is the originally prescribed
geometric point in the prime-field source. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)
  {hden : Nat.Coprime q M.arithmetic.denominator}
  {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g M.arithmetic.base)
  (X : Over M.arithmetic.base) [IsProper X.hom] (a : X ⟶ G.scheme)
  {p : Geometric.PointExt.CM.pointBase (ArithmeticBase.CM.k (q := q)) ⟶ (Over.pullback R.geometricBase).obj X}
  (l : LiftMap.CM.SmoothPoint.IntegralLift X (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.residueIso (q := q))
    (ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p)
  {L : Type} [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L]
  [Algebra (ArithmeticBase.CM.W (q := q)) L] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L)

local notation "t" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.integralBase j M.arithmetic.denominator hden
local notation "w" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.generic_base_compatible j
  M.arithmetic.denominator M.arithmetic.denominator_ne_zero hden
local notation "wr" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QadicModelMap.CM.special_base_compatible j
  M.arithmetic.denominator hden R.residue R.residue_compatibility
local notation "gk" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationResidueTest.CM.geometricBase (q := q)

def equationPoint : Over.mk gk ⟶ (Over.pullback R.specialBase).obj X :=
  ArithmeticEquationPoints.CM.point G a M.arithmetic.generic t w R.specialBase wr V
    (FieldPoint.CM.localTestPoint X l)

theorem equationPoint_recovers_lift :
    equationPoint R G X a l V = Intrinsic.PointFrobenius.CM.pointsEquiv R X p :=
  ReductionPointProjection.CM.Recovery.point_eq_of_projection R.specialBase X (Over.mk gk) _ _
    ((ArithmeticEquationPoints.CM.point_projection G a M.arithmetic.generic t w R.specialBase wr V
      (FieldPoint.CM.localTestPoint X l)).trans
        ((LiftRecovery.CM.specialization_recovers_lift X l V).trans
          (PrimeFieldPoints.CM.pointEquiv_projection R.specialBase gk R.geometricBase
            (Intrinsic.Frobenius.CM.geometricBase_factor R) X p).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EquationPoint.CM
