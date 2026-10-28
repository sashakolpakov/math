import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentPointEquiv
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PointFrobenius

/-! # Ordinary Equiv -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary

noncomputable section

/-! Identify NeighborCounting's native ordinary points with the original
component-labelled points used for detection. The constructed
equivalence intertwines the actual prime-field Frobenius. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.PointFrobenius.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM

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

local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a

theorem ordinary_iff (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a) :
    R.IsOrdinary a (p.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q)))) ↔
      (D).IsOrdinary (PointFrobenius.CM.pointsEquiv R (M.integral a).toOver p) :=
  (FrobeniusKernelLifts.CM.ordinary_iff M hM j hsplit R labels hlabels a p).trans
    (congrArg (D).IsOrdinary (PointFrobenius.CM.pointsEquiv_eq_primeFieldPoint R a p).symm).to_iff

def pointEquiv : Detection.CM.ordinaryPoints R a ≃ (D).OrdinaryPoint :=
  (ComponentPointEquiv.CM.ordinaryEquiv R a).trans
    ((PointFrobenius.CM.pointsEquiv R (M.integral a).toOver).subtypeEquiv
      (ordinary_iff M hM j hsplit R labels hlabels a))

theorem pointEquiv_val (x : Detection.CM.ordinaryPoints R a) :
    (pointEquiv M hM j hsplit R labels hlabels a x).val =
      ReductionPoints.CM.primeFieldPoint R a (x.2.val ≫ Ordinary.Locus.CM.componentFiberInclusion R a x.1) :=
  PointFrobenius.CM.pointsEquiv_eq_primeFieldPoint R a (x.2.val ≫ Ordinary.Locus.CM.componentFiberInclusion R a x.1)

theorem frobenius (hs : Smooth (M.integral a).toOver.hom) (x : Detection.CM.ordinaryPoints R a) :
    pointEquiv M hM j hsplit R labels hlabels a (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs x) =
      (D).ordinaryFrobenius (pointEquiv M hM j hsplit R labels hlabels a x) := by
  apply Subtype.ext
  exact (pointEquiv_val M hM j hsplit R labels hlabels a
    (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hs x)).trans
      ((Ordinary.PointFrobenius.CM.ordinaryFrobenius_total R a hs x).trans
        (congrArg ((AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBaseFrobenius q).hom ≫ ·)
          (pointEquiv_val M hM j hsplit R labels hlabels a x).symm))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary
