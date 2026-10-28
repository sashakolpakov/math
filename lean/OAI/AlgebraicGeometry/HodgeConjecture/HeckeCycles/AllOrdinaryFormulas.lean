import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.PairFormula
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.ReductionFamily
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Ordinary.DetectedPolynomial

/-! # All Ordinary Formulas -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AllOrdinaryFormulas.CM.Ordinary

noncomputable section

/-! Choose actual smooth component lifts and apply native reduction to
obtain the raw ordinary formula for every original same-component pair.
The fixed Hecke types and raw operators are those of the original model. -/

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

open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.Detection.CM

def Formulas (f : Fin 3 → (HD).EndK) : Prop :=
  ∀ (i : Fin 3) (x y : Intrinsic.Detection.CM.ordinaryPoints R a), x.1 = y.1 →
    act (op (f i)) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x - SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a y) =
      ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
        (Ordinary.OperatorTransport.CM.pointOperator e Z) (Ordinary.OperatorTransport.CM.multisetOperator e Y)
        i x).map (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)).sum -
      ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
        (Ordinary.OperatorTransport.CM.pointOperator e Z) (Ordinary.OperatorTransport.CM.multisetOperator e Y)
        i y).map (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)).sum

include hg hIsogenyQuotient in
theorem from_native_reductions (f : Fin 3 → (HD).EndK)
    (hraw : ∀ i : Fin 3, TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) (f i))
    (hreduce : ∀ o : (D).OrdinaryPoint,
      ∀ l : Isogenies.NeighborCounting.Lifts.IntegralLift D (Witt.ArithmeticBase.CM.W (q := q)) (Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden) (Witt.ArithmeticBase.CM.residueIso (q := q)) o.val,
      Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.NativeReductionResult (L := Witt.ArithmeticBase.CM.Generic.F q) (Source.RestrictedPlace.CM.choice M j)
        (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
        active multiplicative hTorsionQuotient (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden)
        (D).ordinaryFrobenius Y Z o l) :
  ∀ (i : Fin 3) (x y : Intrinsic.Detection.CM.ordinaryPoints R a), x.1 = y.1 →
    act (op (f i)) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a x - SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a y) =
      ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
        (Ordinary.OperatorTransport.CM.pointOperator e Z) (Ordinary.OperatorTransport.CM.multisetOperator e Y)
        i x).map (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)).sum -
      ((RepresentationTheory.Hecke.CubicRelation.ordinaryRawNeighbors q (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
        (Ordinary.OperatorTransport.CM.pointOperator e Z) (Ordinary.OperatorTransport.CM.multisetOperator e Y)
        i y).map (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)).sum := by
  classical
  intro i x y hxy
  rcases x with ⟨c, x⟩
  rcases y with ⟨d, y⟩
  change c = d at hxy
  subst d
  let p (b : Bool) : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Ordinary.Locus.CM.componentFiber R a c :=
    if b then x.val else y.val
  have hp (b : Bool) : (p b).left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))) ∈
      Ordinary.Locus.CM.componentOrdinaryLocus R a c := by
    cases b
    · exact y.property
    · exact x.property
  let lc (b : Bool) : Witt.PointLift.CM.ComponentLift R hden a c (p b) :=
    Classical.choice (Witt.PointLift.CM.componentLift_exists R hden a c
      (hgeometry.componentGeometry c).1 (p b))
  exact Ordinary.PairFormula.CM.formula M hM j hsplit R labels hlabels a hden c p hp lc C
    active multiplicative hTorsionQuotient Z Y hg hgeometry hIsogenyQuotient i (f i) (hraw i)
    (fun b => hreduce
      (ComponentOrdinaryPoint.CM.Ordinary.native M hM j hsplit R labels hlabels a c (p b) (hp b))
      (Witt.ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b)))

include hg hIsogenyQuotient in
theorem compact_from_native_reductions (f : Fin 3 → (HD).EndK)
    (hraw : ∀ i : Fin 3, TateComparisonPointEquation.CM.Raw.RawAction HD hgeometry (typ i) (f i))
    (hreduce : Intrinsic.ReductionFamily.CM.IntrinsicFamily.Reductions M hM j hsplit R labels hlabels a hden
      active multiplicative hTorsionQuotient Z Y) :
    Ordinary.DetectedPolynomial.CM.OrdinaryFormulaData.Formulas q (fun z : Intrinsic.Detection.CM.ordinaryPoints R a => z.1) (SpecialOrdinaryFrobenius.CM.Ordinary.ordinaryImage R a)
      (Ordinary.PointFrobenius.CM.ordinaryFrobenius R a hgeometry.smooth)
      (Ordinary.OperatorTransport.CM.pointOperator e Z)
      (Ordinary.OperatorTransport.CM.multisetOperator e Y) (fun i => act (op (f i))) := by
  classical
  intro i x y hxy
  rcases x with ⟨c, x⟩
  rcases y with ⟨d, y⟩
  change c = d at hxy
  subst d
  let p (b : Bool) : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ Ordinary.Locus.CM.componentFiber R a c :=
    if b then x.val else y.val
  have hp (b : Bool) : (p b).left (IsLocalRing.closedPoint (AlgebraicClosure (ZMod q))) ∈
      Ordinary.Locus.CM.componentOrdinaryLocus R a c := by
    cases b
    · exact y.property
    · exact x.property
  let lc (b : Bool) : Witt.PointLift.CM.ComponentLift R hden a c (p b) :=
    Classical.choice (Witt.PointLift.CM.componentLift_exists R hden a c
      (hgeometry.componentGeometry c).1 (p b))
  exact Ordinary.PairFormula.CM.formula M hM j hsplit R labels hlabels a hden c p hp lc C
    active multiplicative hTorsionQuotient Z Y hg hgeometry hIsogenyQuotient i (f i) (hraw i)
    (fun b => hreduce
      (ComponentOrdinaryPoint.CM.Ordinary.native M hM j hsplit R labels hlabels a c (p b) (hp b))
      (Witt.ComponentIntrinsicLift.CM.Intrinsic.nativeLift M hM j hsplit R labels hlabels a hden c (p b) (lc b)))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AllOrdinaryFormulas.CM.Ordinary
