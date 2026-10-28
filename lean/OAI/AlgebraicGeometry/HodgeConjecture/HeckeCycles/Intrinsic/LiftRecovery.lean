import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint

/-! # Lift Recovery -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery.CM

noncomputable section

/-! Express NeighborCounting's actual native PEL lift as the same scheme lift used
in HeckeCycles's specialization equations. Its map is unchanged, and its
reduction is the originally prescribed geometric point. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM

variable {E K : Type} [Field E] [NumberField E] [Algebra ℚ E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
  (R : M.GoodIntegralReduction q j)
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ (v : Fin M.s) (b : Bool),
    labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
  (a : M.Family) (hden : Nat.Coprime q M.arithmetic.denominator)
  (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a)
  (l : Isogenies.NeighborCounting.Lifts.IntegralLift (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a)
    (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden) (Witt.ArithmeticBase.CM.residueIso (q := q)) (ReductionPoints.CM.primeFieldPoint R a p))

def schemeLift : LiftMap.CM.SmoothPoint.IntegralLift (M.integral a).toOver
    (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.residueIso (q := q)) (Witt.ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p where
  map := l.map
  overBase := l.overBase
  reduction := l.reduction.trans
    (congrArg (Spec.map (CommRingCat.ofHom (Witt.ArithmeticBase.CM.residueIso (q := q)).toRingHom) ≫ ·)
      (ReductionPoints.CM.primeFieldPoint_projection R a p))

theorem schemeLift_map : (schemeLift M hM j hsplit R labels hlabels a hden p l).map = l.map := rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery.CM
