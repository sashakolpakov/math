import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPointProjection

/-! # Lift Naturality -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftNaturality.CM

noncomputable section

/-! Generic Witt points commute with morphisms of the original
arithmetic models. In particular, a lift chosen inside a component has
its generic point in that same component of the TateComparison source. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} {R : M.GoodIntegralReduction q j}
  {hden : Nat.Coprime q M.arithmetic.denominator}
  {X Y : Over M.arithmetic.base} (f : X ⟶ Y)
  {p : Geometric.PointExt.CM.pointBase (ArithmeticBase.CM.k (q := q)) ⟶ (Over.pullback R.geometricBase).obj X}
  (l : LiftMap.CM.SmoothPoint.IntegralLift X (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.residueIso (q := q))
    (ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p)
  {L : Type} [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L]

local notation "lf" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.pushforward f (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.residueIso (q := q)) (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p l

theorem fieldPoint_map : FieldPoint.CM.fieldPoint (L := L) Y lf =
    FieldPoint.CM.fieldPoint (L := L) X l ≫ (Over.pullback M.arithmetic.generic).map f := by
  apply ReductionPointProjection.CM.Recovery.point_eq_of_projection M.arithmetic.generic Y
    (Over.mk (EvaluationGenericTest.CM.originalBase (L := L) j))
  have hm : ((Over.pullback M.arithmetic.generic).map f).left ≫ pullback.fst Y.hom M.arithmetic.generic =
      pullback.fst X.hom M.arithmetic.generic ≫ f.left := pullback.lift_fst _ _ _
  have hp := FieldPoint.CM.fieldPoint_projection (L := L) X l
  have hr : (FieldPoint.CM.fieldPoint (L := L) X l ≫
      (Over.pullback M.arithmetic.generic).map f).left ≫ pullback.fst Y.hom M.arithmetic.generic =
      (Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L)) ≫ ArithmeticBase.CM.Generic.fractionBase (q := q) ≫ l.map) ≫ f.left :=
    (Category.assoc _ _ _).trans ((congrArg ((FieldPoint.CM.fieldPoint (L := L) X l).left ≫ ·) hm).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ f.left) hp)))
  refine (FieldPoint.CM.fieldPoint_projection (L := L) Y lf).trans ?_
  simpa only [LiftMap.CM.pushforward, Category.assoc] using hr.symm

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftNaturality.CM
