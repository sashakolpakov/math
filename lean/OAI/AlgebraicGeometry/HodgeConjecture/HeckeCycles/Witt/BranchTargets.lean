import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.ChosenBranchTargets
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.QuotientKernelTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.BranchLabels
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluatedTargetPoint
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingChosenKernel

/-! # Branch Targets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.BranchTargets.CM

noncomputable section

/-! Compare the actual NeighborCounting quotient target with its TateComparison branch.
Both use the same lifted source, chosen subgroups, common multiplier,
polarization and complete level marking. Target equality is deduced
from the proved chosen-kernel uniqueness theorem. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.ReductionSpecification
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic

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
  (p : Geometric.PointExt.CM.pointBase (AlgebraicClosure (ZMod q)) ⟶ R.geometricFiber a)
  (l : Isogenies.NeighborCounting.Lifts.IntegralLift (FrobeniusKernelLifts.CM.reduction M hM j hsplit R labels hlabels a)
    (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.arithmeticMap (j := j) hden) (ArithmeticBase.CM.residueIso (q := q)) (ReductionPoints.CM.primeFieldPoint R a p))

  (C : AbelianScheme.TateComparison.Local.IntegralType M.s → AbelianScheme.TateComparison.Correspondences.EtaleCorrespondence ((Over.pullback M.arithmetic.generic).obj (M.integral a).toOver))
  (active : Fin M.s) (multiplicative : Fin M.s → Bool) (hTorsionQuotient : AbelianScheme.IsogenyQuotient.Unit.Construction.TorsionQuotientInput)

local instance : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
local instance : CharZero (ArithmeticBase.CM.Generic.F q) := EvaluationDVR.CM.fractionCharZero q

local instance heckeProjectorGroup (i : Fin 3) (v : Fin M.s) :
    IsMonHom (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors (Source.RestrictedPlace.CM.choice M j) M.iota
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
      (l.genericPolarized (L := ArithmeticBase.CM.Generic.F q)).abelian (l.genericAction (L := ArithmeticBase.CM.Generic.F q))
      (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels) i v) :=
  (l.genericAction (L := ArithmeticBase.CM.Generic.F q)).preservesGroup
    ((Source.RestrictedPlace.CM.choice M j).projector M.iota
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i)
      (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels (.inl v)))

variable (d : Isogenies.NeighborCounting.Joint.IntrinsicEvaluation.Lifts.JointFiniteEvaluationField (ArithmeticBase.CM.Generic.F q)
  (Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation.neighborEvaluationSchemes (l.genericPolarized (L := ArithmeticBase.CM.Generic.F q)).abelian q active multiplicative
    (Isogenies.NeighborCounting.CMPointsHeckeEvaluation.l45NeighborProjectors (Source.RestrictedPlace.CM.choice M j) M.iota
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit)
      (l.genericPolarized (L := ArithmeticBase.CM.Generic.F q)).abelian (l.genericAction (L := ArithmeticBase.CM.Generic.F q))
      (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)) hTorsionQuotient))

local notation "HD" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))
local notation "sl" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Intrinsic.LiftRecovery.CM.schemeLift M hM j hsplit R labels hlabels a hden p l
local notation "z" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint.CM.fieldPoint (L := d.carrier) (OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IntegralPELSpread.toOver (M.integral a)) sl
local notation "typ" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types.CM.integralType active multiplicative

variable [Algebra (ArithmeticBase.CM.W (q := q)) d.carrier] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) d.carrier]
  (V : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) d.carrier)
  (i : Fin 3) (β : ULift (Fin (d.count (some i))))
  (Q : Isogenies.NeighborCounting.Intrinsic.ReductionSpecification.EvaluatedNativeNeighbor (Source.RestrictedPlace.CM.choice M j)
    (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
    active multiplicative hTorsionQuotient l d V i β)

def targetPoint : (HD).GeometricPoint (EvaluationGenericTest.CM.originalBase (L := d.carrier) j) :=
  EvaluatedTargetPoint.CM.point M hM j hsplit R labels hlabels a hden V Q.target

def quotient : AbelianScheme.TateComparison.PELIsogenies.PELIsogeny ((HD).fiberFamily
    (EvaluationGenericTest.CM.originalBase (L := d.carrier) j) z)
    ((HD).fiberFamily (EvaluationGenericTest.CM.originalBase (L := d.carrier) j)
      (targetPoint M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d V i β Q))
    (q ^ (typ i).multiplierNat) :=
  (Q.quotient.transport
    (PELSource.CM.sourceIso M hM j hsplit R labels hlabels a hden p l C
      (fun w => j.localCharacter M.extendedEmbedding (labels w))).symm
    (EvaluatedTargetPoint.CM.familyIso M hM j hsplit R labels hlabels a hden V Q.target C
      (fun w => j.localCharacter M.extendedEmbedding (labels w)))).castMultiplier
    (congrArg (fun n => q ^ n) (Neighbor.Types.CM.multiplier active multiplicative i).symm)

theorem quotient_chosen_kernel (v : Fin M.s) :
    (AbelianScheme.TateComparison.Subgroups.PointSubgroup.kernel (CM.quotient M hM j hsplit R labels hlabels a hden p l C active multiplicative
      hTorsionQuotient d V i β Q).isogeny.hom).inf
      (AbelianScheme.TateComparison.Subgroups.splitBlock ((HD).fiberFamily (EvaluationGenericTest.CM.originalBase (L := d.carrier) j) z)
        ((HD).localCharacter (v, false)) (typ i).multiplierNat) =
      (BranchLabels.CM.kernelEquiv M hM j hsplit R labels hlabels a hden p l C
        active multiplicative hTorsionQuotient d i β).val v :=
  QuotientKernelTransport.CM.splitKernel Q.quotient
    (PELSource.CM.sourceIso M hM j hsplit R labels hlabels a hden p l C
      (fun w => j.localCharacter M.extendedEmbedding (labels w)))
    (EvaluatedTargetPoint.CM.familyIso M hM j hsplit R labels hlabels a hden V Q.target C
      (fun w => j.localCharacter M.extendedEmbedding (labels w)))
    (funext fun v => Source.RestrictedPlace.CM.localCharacter_eq M j (labels (v, false)))
    (Neighbor.Types.CM.multiplier active multiplicative i).symm
    (Neighbor.Types.CM.exponents active multiplicative i).symm
    (Neighbor.CountingKernelParameters.CM.kernelEquiv (Source.RestrictedPlace.CM.choice M j)
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
      active multiplicative hTorsionQuotient l d i β)
    (Neighbor.CountingChosenKernel.CM.quotient_chosen_kernel (Source.RestrictedPlace.CM.choice M j)
      (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
      active multiplicative hTorsionQuotient l d V i β Q) v

variable
  (hg : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime)
  (hgeometry : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

include hg hgeometry hIsogenyQuotient in
theorem target_eq :
    targetPoint M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d V i β Q =
      ((HD).correspondence (typ i)).endpoint
        (BranchLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
          active multiplicative hTorsionQuotient d hIsogenyQuotient i β) :=
  Finite.ChosenBranchTargets.CM.target_eq (k := d.carrier)
    (b := EvaluationGenericTest.CM.originalBase (L := d.carrier) j)
    (I := ULift (Fin (d.count (some i)))) (HD) hg hgeometry hM.2.1 hM.1 hIsogenyQuotient (typ i) z
    (BranchLabels.CM.kernelEquiv M hM j hsplit R labels hlabels a hden p l C
      active multiplicative hTorsionQuotient d i) β
    (targetPoint M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d V i β Q)
    (CM.quotient M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d V i β Q)
    (quotient_chosen_kernel M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d V i β Q)

include hg hgeometry hIsogenyQuotient in
theorem target_projection :
    Q.target.map =
      (((HD).correspondence (typ i)).endpoint
        (BranchLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
          active multiplicative hTorsionQuotient d hIsogenyQuotient i β)).left ≫
        CategoryTheory.Limits.pullback.fst (M.integral a).toOver.hom M.arithmetic.generic :=
  (EvaluatedTargetPoint.CM.point_projection M hM j hsplit R labels hlabels a hden V Q.target).symm.trans
    (congrArg (fun y => y.left ≫ CategoryTheory.Limits.pullback.fst
      (M.integral a).toOver.hom M.arithmetic.generic)
      (target_eq M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d V i β Q
        hg hgeometry hIsogenyQuotient))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.BranchTargets.CM
