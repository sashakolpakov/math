import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.PELSource
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Source.RestrictedPlace
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingKernelParameters
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceTransport
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.KernelChoiceIndices
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.Types
import OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels

/-! # Branch Labels -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.BranchLabels.CM

noncomputable section

/-! Match NeighborCounting's actual evaluated labels bijectively with TateComparison's
branches through the actual generic point of the same Witt lift. The
source PEL isomorphism, characters, multiplier and exponents are proved.
No branch-matching hypothesis occurs. -/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open scoped _root_.CategoryTheory.MonObj
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.HeckeExponents OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.HeckeEvaluation
open OAI.AlgebraicGeometry.Isogenies.NeighborCounting.CMPointsHeckeEvaluation OAI.AlgebraicGeometry.Isogenies.NeighborCounting.Intrinsic.KernelLabels
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

def kernelEquiv (i : Fin 3) : ULift (Fin (d.count (some i))) ≃ (HD).chosenKernels (typ i) z :=
  (Neighbor.CountingKernelParameters.CM.kernelEquiv (Source.RestrictedPlace.CM.choice M j)
    (Source.RestrictedPlace.CM.splitCoordinates M j hsplit) (Isogenies.NeighborCounting.Intrinsic.KernelLabels.nativeKernelLabels labels)
    active multiplicative hTorsionQuotient l d i).trans
    ((KernelChoiceTransport.CM.choiceEquiv
      (PELSource.CM.sourceIso M hM j hsplit R labels hlabels a hden p l C
        (fun w => j.localCharacter M.extendedEmbedding (labels w)))
      (fun v => (Source.RestrictedPlace.CM.choice M j).localCharacter M.iota (labels (v, false)))
      (Isogenies.NeighborCounting.HeckeExponents.neighborLevel i) (Isogenies.NeighborCounting.HeckeExponents.neighborExponents active multiplicative i)).trans
      (KernelChoiceIndices.CM.choiceEquiv ((HD).fiberFamily
        (EvaluationGenericTest.CM.originalBase (L := d.carrier) j) z)
        (funext fun v => Source.RestrictedPlace.CM.localCharacter_eq M j (labels (v, false)))
        (Neighbor.Types.CM.multiplier active multiplicative i).symm
        (Neighbor.Types.CM.exponents active multiplicative i).symm))

def branchEquiv (hIsogenyQuotient : (HD).RealizesIsogenyQuotient) (i : Fin 3) :
    ULift (Fin (d.count (some i))) ≃ ((HD).correspondence (typ i)).Fiber z :=
  (kernelEquiv M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d i).trans
    ((HD).c46FiberKernelEquiv hIsogenyQuotient (typ i) z).symm

theorem branchEquiv_kernel (hIsogenyQuotient : (HD).RealizesIsogenyQuotient) (i : Fin 3)
    (b : ULift (Fin (d.count (some i)))) :
    (HD).c46FiberKernelEquiv hIsogenyQuotient (typ i) z
      (branchEquiv M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d hIsogenyQuotient i b) =
        kernelEquiv M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d i b :=
  ((HD).c46FiberKernelEquiv hIsogenyQuotient (typ i) z).apply_symm_apply _

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.BranchLabels.CM
