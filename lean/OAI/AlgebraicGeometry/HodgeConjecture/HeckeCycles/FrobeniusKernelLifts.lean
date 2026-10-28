import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase
import OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Lifts

/-! # Frobenius Kernel Lifts -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM

noncomputable section

/-! Assemble the native FrobeniusKernel reduction and NeighborCounting polarized point lift
from the actual IntegralModel/CMPoints model. The ordinary point and the residue map
are identified with the original source, rather than supplied anew. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction
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
  (a : M.Family)

abbrev reduction := AbelianScheme.FrobeniusKernel.CMPointsReductionAdapter.Construction.l45SplitPELReduction M hM j hsplit R labels hlabels a

theorem ordinary_iff (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a) :
    R.IsOrdinary a (p.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q)))) ↔
      (CM.reduction M hM j hsplit R labels hlabels a).IsOrdinary (ReductionPoints.CM.primeFieldPoint R a p) := by
  obtain ⟨_, _, _, _, _, _, hs, _, _, _⟩ := hM.2.2 a
  exact ReductionPoints.CM.isOrdinary_iff_primeFieldPoint_count R a hs p

variable (hden : Nat.Coprime q M.arithmetic.denominator)

theorem residueCompatible :
    Isogenies.NeighborCounting.Lifts.ResidueCompatible (CM.reduction M hM j hsplit R labels hlabels a)
      (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden) (Witt.ArithmeticBase.CM.residueIso (q := q)) :=
  Witt.ArithmeticBase.CM.residue_compatible R hden

def nativeLift (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a) :
    Isogenies.NeighborCounting.Lifts.IntegralLift (CM.reduction M hM j hsplit R labels hlabels a)
      (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden) (Witt.ArithmeticBase.CM.residueIso (q := q)) (ReductionPoints.CM.primeFieldPoint R a p) := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal (Witt.ArithmeticBase.CM.W (q := q))) (Witt.ArithmeticBase.CM.W (q := q)) :=
    Witt.LiftBase.CM.complete q (AlgebraicClosure (ZMod q))
  exact Isogenies.NeighborCounting.Lifts.integralLift (CM.reduction M hM j hsplit R labels hlabels a)
    (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden) (Witt.ArithmeticBase.CM.residueIso (q := q))
    (residueCompatible M hM j hsplit R labels hlabels a hden) (ReductionPoints.CM.primeFieldPoint R a p)

theorem nativeLift_reduction (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a) :
    Spec.map (CommRingCat.ofHom (IsLocalRing.residue (Witt.ArithmeticBase.CM.W (q := q)))) ≫
      (nativeLift M hM j hsplit R labels hlabels a hden p).map =
        Spec.map (CommRingCat.ofHom (Witt.ArithmeticBase.CM.residueIso (q := q)).toRingHom) ≫ p.left ≫ R.projection a := by
  exact (nativeLift M hM j hsplit R labels hlabels a hden p).reduction.trans
    (congrArg (Spec.map (CommRingCat.ofHom (Witt.ArithmeticBase.CM.residueIso (q := q)).toRingHom) ≫ ·)
      (ReductionPoints.CM.primeFieldPoint_projection R a p))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM
