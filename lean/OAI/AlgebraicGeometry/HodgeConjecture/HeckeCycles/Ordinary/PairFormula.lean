import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.CommonPairFormula
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ComponentEvaluation
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.CountImages

/-! # Pair Formula -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PairFormula.CM

noncomputable section

/-! The actual native reduction output gives the ordinary TateComparison pair
formula on the original component. The common evaluation, source and
target images, Frobenius and all raw multiplicities are derived. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj _root_.CategoryTheory.Obj
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
  (p : Bool → (Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Locus.CM.componentFiber R a c))
  (hord : ∀ b, (p b).left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))) ∈ Locus.CM.componentOrdinaryLocus R a c)
  (lc : ∀ b, Witt.PointLift.CM.ComponentLift R hden a c (p b))

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.TateComparisonPointEquation.CM.Raw

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (Witt.ArithmeticBase.CM.Generic.F q) := Witt.EvaluationDVR.CM.fractionCharZero q

variable
  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (active : Fin M.s) (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.SpecialOrdinaryFrobenius.CM.Ordinary

variable
  (Z : (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)
  (Y : (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint →
    Multiset (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a).OrdinaryPoint)
  (hg : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime)
  (hgeometry : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (Witt.PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative
local notation "D" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a
local notation "e" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.OrdinaryEquiv.CM.IntrinsicOrdinary.pointEquiv M hM j hsplit R labels hlabels a
local notation "op" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EquationValues.CM.Hecke.originalOperator M j R a hden C
  (fun w => j.localCharacter M.extendedEmbedding (labels w)) hgeometry
local notation "act" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.PointEvaluation.CM.action (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Frobenius.CM.specialAlbanese R a) (OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q)

def original (b : Bool) := ComponentOrdinaryPoint.CM.Ordinary.original M j R a c (p b) (hord b)

def ordinarySum (b : Bool) (i : Fin 3) :
    Additive (AbelianScheme.FrobeniusKernel.ModuliPoint.Construction.geometricBase q ⟶ (Intrinsic.Frobenius.CM.specialAlbanese R a).X) :=
  ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q (PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
    (OperatorTransport.CM.pointOperator e Z) (OperatorTransport.CM.multisetOperator e Y)
    i (original M j R a c p hord b)).map (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)).sum

def Formula (f : (HD).EndK) (i : Fin 3) : Prop :=
  act (op f) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a (original M j R a c p hord true) -
    SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a (original M j R a c p hord false)) =
    ordinarySum M hM j hsplit R labels hlabels a c p hord C Z Y hgeometry true i -
      ordinarySum M hM j hsplit R labels hlabels a c p hord C Z Y hgeometry false i

include hg hIsogenyQuotient in
theorem formula (i : Fin 3) (f : (HD).EndK) (hraw : TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) f)
    (hreduce : ∀ b, Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := Witt.ArithmeticBase.CM.Generic.F q) (Source.RestrictedPlace.CM.choice M j)
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
      active multiplicative hTorsionQuotient (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden)
      (D).ordinaryFrobenius Y Z
      (ComponentOrdinaryPoint.CM.Ordinary.native M hM j hsplit R labels hlabels a c (p b) (hord b))
      (Witt.ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b))) :
    act (op f) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a (original M j R a c p hord true) -
      SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a (original M j R a c p hord false)) =
      ordinarySum M hM j hsplit R labels hlabels a c p hord C Z Y hgeometry true i -
        ordinarySum M hM j hsplit R labels hlabels a c p hord C Z Y hgeometry false i := by
  classical
  choose data hdata using fun b => ComponentEvaluation.CM.exists_evaluation M hM j hsplit R labels hlabels a hden
    c (p b) (hord b) (lc b) active multiplicative hTorsionQuotient Z Y (hreduce b)
  have hp := CommonPairFormula.CM.formula M hM j hsplit R labels hlabels a hden c p lc C
    active multiplicative hTorsionQuotient data hg hgeometry hIsogenyQuotient i f hraw
  have hx := ComponentOrdinaryPoint.CM.Ordinary.image_eq M j R a c (p true) (hord true)
  have hy := ComponentOrdinaryPoint.CM.Ordinary.image_eq M j R a c (p false) (hord false)
  have hr (b : Bool) := Intrinsic.CountImages.CM.from_native_counts M hM j hsplit R labels hlabels a
    hgeometry.smooth Z Y i (original M j R a c p hord b) _ (hdata b i)
  exact (congrArg (act (op f)) (congrArg₂ (fun u v => u - v) hx.symm hy.symm)).trans
    (hp.trans (congrArg₂ (fun u v => u - v) (hr true) (hr false)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PairFormula.CM
