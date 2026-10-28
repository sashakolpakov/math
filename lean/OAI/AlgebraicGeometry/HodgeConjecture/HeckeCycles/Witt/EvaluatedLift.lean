import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationBaseSquare
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftBaseChange

/-! # Evaluated Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluatedLift.CM

noncomputable section

/-! Extend the actual Witt lift to the constructed evaluation DVR,
over precisely the integral q-adic source base used for specialization. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluationDVR.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.LiftMap.CM.SmoothPoint

variable {q : ℕ} [Fact q.Prime] {L : Type} [Field L] [Algebra (ArithmeticBase.CM.W (q := q)) L]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L)
  {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  {M : PELModuli.CMPoints.Models.RankThreePELModel E K} {j : M.QadicChoice q}
  (hden : Nat.Coprime q M.arithmetic.denominator)

theorem arithmetic_square :
    Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.W (q := q)) V.carrier)) ≫ ArithmeticBase.CM.wittBase (j := j) hden =
      EvaluationBaseSquare.CM.integralBase V ≫
        QadicModelMap.CM.integralBase j M.arithmetic.denominator hden := by
  calc
    _ = EvaluationDVR.CM.evaluatedBase (j := j) V hden := by
      change Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.W (q := q)) V.carrier)) ≫
          Spec.map (CommRingCat.ofHom (ArithmeticBase.CM.arithmeticMap (j := j) hden)) =
        Spec.map (CommRingCat.ofHom (EvaluationDVR.CM.evaluatedArithmeticMap (j := j) V hden))
      rw [← Spec.map_comp]
      rfl
    _ = _ := (EvaluationBaseSquare.CM.arithmetic_square V hden).symm

variable (X : Over M.arithmetic.base) {bk : Spec (.of (ArithmeticBase.CM.k (q := q))) ⟶ M.arithmetic.base}
  {p : Geometric.PointExt.CM.pointBase (ArithmeticBase.CM.k (q := q)) ⟶ (Over.pullback bk).obj X}
  (l : LiftMap.CM.SmoothPoint.IntegralLift X (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.residueIso (q := q)) (ArithmeticBase.CM.wittBase (j := j) hden) bk p)

def evaluatedLift : LiftMap.CM.SmoothPoint.IntegralLift X V.carrier (EvaluationDVR.CM.geometricResidueIso V)
    (EvaluationBaseSquare.CM.integralBase V ≫
      QadicModelMap.CM.integralBase j M.arithmetic.denominator hden) bk p := by
  let l' := LiftBaseChange.CM.baseChange l (algebraMap (ArithmeticBase.CM.W (q := q)) V.carrier)
    V.residueIso V.residue_compatible
  exact ⟨l'.map, l'.overBase.trans (arithmetic_square V hden), l'.reduction⟩

theorem evaluatedLift_map :
    (evaluatedLift V hden X l).map =
      Spec.map (CommRingCat.ofHom (algebraMap (ArithmeticBase.CM.W (q := q)) V.carrier)) ≫ l.map := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.EvaluatedLift.CM
