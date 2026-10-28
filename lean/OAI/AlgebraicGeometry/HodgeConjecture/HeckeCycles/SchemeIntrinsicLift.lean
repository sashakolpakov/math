import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery

/-! # Scheme Intrinsic Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SchemeIntrinsicLift.CM.Intrinsic

noncomputable section

/-! A chosen scheme lift into the original PEL model is itself a native
NeighborCounting lift. This lets the source lift be chosen inside its original
connected component before invoking the full native reduction theorem. -/

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
  (l : LiftMap.CM.SmoothPoint.IntegralLift (M.integral a).toOver
    (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.residueIso (q := q)) (Witt.ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p)

def nativeLift : Isogenies.NeighborCounting.Lifts.IntegralLift (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a)
    (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden) (Witt.ArithmeticBase.CM.residueIso (q := q)) (ReductionPoints.CM.primeFieldPoint R a p) where
  map := l.map
  overBase := l.overBase
  reduction := l.reduction.trans
    (congrArg (Spec.map (CommRingCat.ofHom (Witt.ArithmeticBase.CM.residueIso (q := q)).toRingHom) ≫ ·)
      (ReductionPoints.CM.primeFieldPoint_projection R a p).symm)

theorem schemeLift_nativeLift :
    Intrinsic.LiftRecovery.CM.schemeLift M hM j hsplit R labels hlabels a hden p
      (nativeLift M hM j hsplit R labels hlabels a hden p l) = l := by
  cases l
  rfl

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SchemeIntrinsicLift.CM.Intrinsic
