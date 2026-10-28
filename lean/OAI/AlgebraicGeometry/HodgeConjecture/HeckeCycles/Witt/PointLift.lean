import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus

/-! # Point Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PointLift.CM

noncomputable section

/-! Every actual geometric point of the smooth IntegralModel model lifts over
the canonical Witt DVR, using the exact residue map chosen by CMPoints.
This includes the points in each ordinary component used for detection. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} (R : M.GoodIntegralReduction q j)
  (hden : Nat.Coprime q M.arithmetic.denominator) (a : M.Family)

abbrev IntegralLift (p : Geometric.PointExt.CM.pointBase (ArithmeticBase.CM.k (q := q)) ⟶ R.geometricFiber a) :=
  LiftMap.CM.SmoothPoint.IntegralLift (M.integral a).toOver (ArithmeticBase.CM.W (q := q))
    (ArithmeticBase.CM.residueIso (q := q)) (ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p

theorem integralLift_exists (hs : Smooth (M.integral a).toOver.hom)
    (p : Geometric.PointExt.CM.pointBase (ArithmeticBase.CM.k (q := q)) ⟶ R.geometricFiber a) :
    Nonempty (IntegralLift R hden a p) := by
  let : Smooth (M.integral a).toOver.hom := hs
  let : IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticBase.CM.W (q := q))) (ArithmeticBase.CM.W (q := q)) :=
    LiftBase.CM.complete q (ArithmeticBase.CM.k (q := q))
  exact LiftMap.CM.SmoothPoint.integralLift_exists (M.integral a).toOver (ArithmeticBase.CM.W (q := q))
    (ArithmeticBase.CM.residueIso (q := q)) (ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase
    (ArithmeticBase.CM.geometric_square R hden) p

abbrev ComponentLift (i : Fin (M.componentCount a))
    (p : Geometric.PointExt.CM.pointBase (ArithmeticBase.CM.k (q := q)) ⟶ Ordinary.Locus.CM.componentFiber R a i) :=
  LiftMap.CM.SmoothPoint.IntegralLift ((M.components a).S i) (ArithmeticBase.CM.W (q := q))
    (ArithmeticBase.CM.residueIso (q := q)) (ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p

theorem componentLift_exists (i : Fin (M.componentCount a))
    (hs : Smooth ((M.components a).S i).hom)
    (p : Geometric.PointExt.CM.pointBase (ArithmeticBase.CM.k (q := q)) ⟶ Ordinary.Locus.CM.componentFiber R a i) :
    Nonempty (ComponentLift R hden a i p) := by
  let : Smooth ((M.components a).S i).hom := hs
  let : IsAdicComplete (IsLocalRing.maximalIdeal (ArithmeticBase.CM.W (q := q))) (ArithmeticBase.CM.W (q := q)) :=
    LiftBase.CM.complete q (ArithmeticBase.CM.k (q := q))
  exact LiftMap.CM.SmoothPoint.integralLift_exists ((M.components a).S i) (ArithmeticBase.CM.W (q := q))
    (ArithmeticBase.CM.residueIso (q := q)) (ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase
    (ArithmeticBase.CM.geometric_square R hden) p

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PointLift.CM
