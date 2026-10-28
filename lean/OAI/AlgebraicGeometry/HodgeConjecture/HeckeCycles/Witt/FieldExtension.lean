import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlgebraFieldTest

/-! # Field Extension -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldExtension.CM

noncomputable section

/-! The actual Witt lift gives the same generic source point after a
field embedding over the Witt fraction field, on the canonical
arithmetic test. No new source lift is chosen. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {q : ℕ} [Fact q.Prime]
  {j : M.QadicChoice q} {R : M.GoodIntegralReduction q j}
  {hden : Nat.Coprime q M.arithmetic.denominator}
  (X : Over M.arithmetic.base)
  {p : Geometric.PointExt.CM.pointBase (ArithmeticBase.CM.k (q := q)) ⟶ (Over.pullback R.geometricBase).obj X}
  (l : LiftMap.CM.SmoothPoint.IntegralLift X (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.residueIso (q := q))
    (ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p)
  {L : Type} [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L]

  {L' : Type} [Field L'] [Algebra (ArithmeticBase.CM.Generic.F q) L'] (σ : L →ₐ[ArithmeticBase.CM.Generic.F q] L')

theorem fieldPoint_natural :
    AlgebraFieldTest.CM.map (ArithmeticBase.CM.Generic.numberFieldBase j) σ ≫ FieldPoint.CM.fieldPoint (L := L) X l =
      FieldPoint.CM.fieldPoint (L := L') X l :=
  (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ LiftedGenericPoints.CM.genericPoint X l)
      (AlgebraFieldTest.CM.source_square (ArithmeticBase.CM.Generic.numberFieldBase j) σ))

theorem reindexed_fieldPoint :
    (AlgebraFieldTest.CM.testIso (ArithmeticBase.CM.Generic.numberFieldBase j) σ).hom ≫
      (FieldPointDescent.CM.testMap σ.toRingHom (EvaluationGenericTest.CM.originalBase (L := L) j) ≫
        FieldPoint.CM.fieldPoint (L := L) X l) = FieldPoint.CM.fieldPoint (L := L') X l :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ FieldPoint.CM.fieldPoint (L := L) X l)
      (AlgebraFieldTest.CM.map_eq (ArithmeticBase.CM.Generic.numberFieldBase j) σ).symm).trans (fieldPoint_natural X l σ))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldExtension.CM
