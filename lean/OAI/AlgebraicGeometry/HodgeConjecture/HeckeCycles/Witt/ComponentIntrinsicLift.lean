import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SchemeIntrinsicLift
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.LiftNaturality
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource
import OAI.AlgebraicGeometry.AbelianScheme.TateComparison.Interface

/-! # Component Intrinsic Lift -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ComponentIntrinsicLift.CM.Intrinsic

noncomputable section

/-! Construct the native NeighborCounting source lift from a lift inside the
original IntegralModel component. Its generic point lies in that identical
component of the actual TateComparison model over every evaluation field. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM

variable {E K : Type} [Field E] [NumberField E]
  [NumberField.IsCMField E] [Field K] [NumberField K]
  (M : PELModuli.CMPoints.Models.RankThreePELModel E K) (hM : M.HasPrescribedBallPeriods)
  {q : ℕ} [Fact q.Prime] (j : M.QadicChoice q)
  (hsplit : j.HasSplitCoordinates M.extendedEmbedding)
  (R : M.GoodIntegralReduction q j)
  (labels : (Fin M.s × Bool) ≃ Gal(E/ℚ))
  (hlabels : ∀ (v : Fin M.s) (b : Bool),
    labels (v, !b) = PELModuli.CMPoints.Arithmetic.rationalConjugation E * labels (v, b))
  (a : M.Family) (hden : Nat.Coprime q M.arithmetic.denominator)
  (c : Fin (M.componentCount a))
  (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Ordinary.Locus.CM.componentFiber R a c)
  (lc : PointLift.CM.ComponentLift R hden a c p)

local notation "inc" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.Locus.CM.componentInclusion (M.components a) (M.decomposition a) c

def point : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a :=
  p ≫ Ordinary.Locus.CM.componentFiberInclusion R a c

def schemeLift : PointLift.CM.IntegralLift R hden a (point M j R a c p) :=
  LiftMap.CM.pushforward inc (ArithmeticBase.CM.residueIso (q := q)) (ArithmeticBase.CM.wittBase (j := j) hden) R.geometricBase p lc

def nativeLift := SchemeIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden
  (point M j R a c p) (schemeLift M j R a hden c p lc)

variable {L : Type} [Field L] [Algebra (ArithmeticBase.CM.Generic.F q) L]
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (χ : Fin M.s × Bool → NumberField.RingOfIntegers E →+* ℤ_[q])

theorem fieldPoint_component :
    FieldPoint.CM.fieldPoint (L := L) (M.integral a).toOver
      (Intrinsic.LiftRecovery.CM.schemeLift M hM j hsplit R labels hlabels a hden (point M j R a c p)
        (nativeLift M hM j hsplit R labels hlabels a hden c p lc)) =
    FieldPoint.CM.fieldPoint (L := L) ((M.components a).S c) lc ≫
      (PELSource.CM.heckeData M a C χ).componentInclusion c := by
  have h := SchemeIntrinsicLift.CM.Intrinsic.schemeLift_nativeLift M hM j hsplit R labels hlabels a hden
    (point M j R a c p) (schemeLift M j R a hden c p lc)
  have hp := congrArg (fun l' => FieldPoint.CM.fieldPoint (L := L) (M.integral a).toOver l') h
  exact hp.trans (LiftNaturality.CM.fieldPoint_map (L := L) inc lc)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ComponentIntrinsicLift.CM.Intrinsic
