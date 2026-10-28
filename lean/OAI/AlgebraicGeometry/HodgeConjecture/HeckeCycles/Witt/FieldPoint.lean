import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftedGenericPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationFractionSquare
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluatedLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent

/-! # Field Point -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint.CM

noncomputable section

/-! Extend the generic point of the prescribed Witt lift to the actual
evaluation field. Reindexing to the q-adic test preserves its arithmetic
projection, which is the generic point of the constructed evaluated lift. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
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

def fieldPoint : Over.mk (EvaluationGenericTest.CM.originalBase (L := L) j) ⟶
    (Over.pullback M.arithmetic.generic).obj X :=
  FieldPointDescent.CM.testMap (algebraMap (ArithmeticBase.CM.Generic.F q) L) (ArithmeticBase.CM.Generic.numberFieldBase j) ≫
    LiftedGenericPoints.CM.genericPoint X l

theorem fieldPoint_projection :
    (fieldPoint X l (L := L)).left ≫ pullback.fst X.hom M.arithmetic.generic =
      Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L)) ≫ ArithmeticBase.CM.Generic.fractionBase (q := q) ≫ l.map := by
  change (Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L)) ≫
    (LiftedGenericPoints.CM.genericPoint X l).left) ≫ _ = _
  rw [Category.assoc, LiftedGenericPoints.CM.genericPoint_projection]

def localTestPoint :
    (Over.map (Spec.map (CommRingCat.ofHom (QadicModelMap.CM.localFieldEmbedding j)))).obj
      (Over.mk (EvaluationBaseSquare.CM.fieldBase (L := L) (q := q))) ⟶
    (Over.pullback M.arithmetic.generic).obj X :=
  (EvaluationGenericTest.CM.testIso (L := L) j).hom ≫ fieldPoint X l

theorem localTestPoint_projection :
    (localTestPoint X l (L := L)).left ≫ pullback.fst X.hom M.arithmetic.generic =
      Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.Generic.F q) L)) ≫ ArithmeticBase.CM.Generic.fractionBase (q := q) ≫ l.map := by
  change ((EvaluationGenericTest.CM.testIso (L := L) j).hom.left ≫
    (fieldPoint X l).left) ≫ _ = _
  rw [EvaluationGenericTest.CM.testIso_hom_left]
  exact (congrArg (fun m => m ≫ pullback.fst X.hom M.arithmetic.generic)
    (Category.id_comp (fieldPoint X l (L := L)).left)).trans (fieldPoint_projection X l)

variable [Algebra (ArithmeticBase.CM.W (q := q)) L] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L)

theorem evaluatedLift_projection :
    (localTestPoint X l (L := L)).left ≫ pullback.fst X.hom M.arithmetic.generic =
      ValuativePoints.CM.genericBase (R := V.carrier) (L := L) ≫
        (EvaluatedLift.CM.evaluatedLift V hden X l).map := by
  rw [localTestPoint_projection, EvaluatedLift.CM.evaluatedLift_map,
    ← Category.assoc, EvaluationFractionSquare.CM.fraction_square V, Category.assoc]

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint.CM
