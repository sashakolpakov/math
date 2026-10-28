import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentOrdinaryPoint
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.EvaluationData
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

/-! # Component Evaluation -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentEvaluation.CM

noncomputable section

/-! Extract the actual native evaluation of a lift in the original
ordinary component. Its exact count formula uses the same original
component-labelled ordinary point under the proved point equivalence. -/

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

  (hord : p.left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))) ∈ Ordinary.Locus.CM.componentOrdinaryLocus R a c)

  (lc : Witt.PointLift.CM.ComponentLift R hden a c p)
  (active : Fin M.s) (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (Witt.ArithmeticBase.CM.Generic.F q) := Witt.EvaluationDVR.CM.fractionCharZero q

variable
  (Z : (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)
  (Y : (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    Multiset (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)

local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a
local notation "J" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace.CM.choice M j
local notation "split" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace.CM.splitCoordinates M j hsplit
local notation "l" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c p lc
local notation "np" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentOrdinaryPoint.CM.Ordinary.native M hM j hsplit R labels hlabels a c p hord
local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentOrdinaryPoint.CM.Ordinary.original M j R a c p hord
local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary.pointEquiv M hM j hsplit R labels hlabels a
local notation "hbase" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden

theorem exists_evaluation
    (h : Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := Witt.ArithmeticBase.CM.Generic.F q) J split (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) active multiplicative hTorsionQuotient
      hbase (D).ordinaryFrobenius Y Z np l) :
    ∃ data : Intrinsic.EvaluationData.CM.Evaluation (L := Witt.ArithmeticBase.CM.Generic.F q) J split (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
      active multiplicative hTorsionQuotient l,
      ∀ i : Fin 3,
        Intrinsic.EvaluationData.CM.reducedNeighbors J split (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) active multiplicative hTorsionQuotient l data hbase i =
          (RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors (O := (D).OrdinaryPoint) q (D).ordinaryFrobenius Z Y i (e op)).map Subtype.val := by
  obtain ⟨data, hdata⟩ := Intrinsic.EvaluationData.CM.exists_evaluation (L := Witt.ArithmeticBase.CM.Generic.F q) J split (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
    active multiplicative hTorsionQuotient hbase (D).ordinaryFrobenius Z Y np l h
  refine ⟨data, fun i => (hdata i).trans ?_⟩
  exact congrArg (fun u => (RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors (O := (D).OrdinaryPoint) q (D).ordinaryFrobenius Z Y i u).map Subtype.val)
    (ComponentOrdinaryPoint.CM.Ordinary.native_eq M hM j hsplit R labels hlabels a c p hord)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentEvaluation.CM
