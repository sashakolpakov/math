import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.BranchLabels
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.SourceExtension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingParameterCoordinates
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Finite.BranchEnumeration

/-! # Extended Labels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ExtendedLabels.CM

noncomputable section

/-! The original NeighborCounting evaluated labels exhaust TateComparison's branches after
further field extension. The cardinality is proved again from the same
represented parameter scheme; injective field extension then gives the
bijection preserving each original branch target and its multiplicity. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Geometric.PointExt.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.ReductionPoints.CM
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic
open OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM

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

variable {L' : Type} [Field L'] (σ : d.carrier →+* L')

local notation "extBase" => Spec.map (CommRingCat.ofHom σ) ≫ OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM.originalBase (L := d.carrier) j
local notation "extPoint" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM.testMap σ (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM.originalBase (L := d.carrier) j) ≫ z

def kernelEquiv (i : Fin 3) : ULift (Fin (d.count (some i))) ≃ (HD).chosenKernels (typ i) extPoint :=
  (Neighbor.CountingParameterCoordinates.CM.extendedKernelEquiv (Source.RestrictedPlace.CM.choice M j)
    (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
    active multiplicative hTorsionQuotient l d σ i).trans
    ((KernelChoiceTransport.CM.choiceEquiv
      (SourceExtension.CM.sourceIso M hM j hsplit R labels hlabels a hden p l C
        (fun w => j.localCharacter M.extendedEmbedding (labels w)) σ)
      (fun v => (Source.RestrictedPlace.CM.choice M j).localCharacter M.iota (labels (v, false)))
      (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i)).trans
      (KernelChoiceIndices.CM.choiceEquiv ((HD).fiberFamily extBase extPoint)
        (funext fun v => Source.RestrictedPlace.CM.localCharacter_eq M j (labels (v, false)))
        (Neighbor.Types.CM.multiplier active multiplicative i).symm
        (Neighbor.Types.CM.exponents active multiplicative i).symm))

variable (hIsogenyQuotient : (PELSource.CM.heckeData M a C
  (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

def branchEquiv (i : Fin 3) : ULift (Fin (d.count (some i))) ≃ ((HD).correspondence (typ i)).Fiber extPoint :=
  (kernelEquiv M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d σ i).trans
    ((HD).c46FiberKernelEquiv hIsogenyQuotient (typ i) extPoint).symm

include hIsogenyQuotient in
theorem geometric_neighbors_eq [IsAlgClosed L'] (i : Fin 3) :
    ((HD).correspondence (typ i)).neighbors extBase extPoint =
      (Finset.univ.val.map (fun β : ULift (Fin (d.count (some i))) =>
        ((HD).correspondence (typ i)).endpoint
          (BranchLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
            active multiplicative hTorsionQuotient d hIsogenyQuotient i β))).map
        (fun y => FieldPointDescent.CM.testMap σ (EvaluationGenericTest.CM.originalBase (L := d.carrier) j) ≫ y) :=
  Finite.BranchEnumeration.CM.neighbors_eq_original_targets ((HD).correspondence (typ i)) z
    (BranchLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
      active multiplicative hTorsionQuotient d hIsogenyQuotient i) extBase
    (FieldPointDescent.CM.testMap σ (EvaluationGenericTest.CM.originalBase (L := d.carrier) j))
    (branchEquiv M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d σ hIsogenyQuotient i)

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ExtendedLabels.CM
