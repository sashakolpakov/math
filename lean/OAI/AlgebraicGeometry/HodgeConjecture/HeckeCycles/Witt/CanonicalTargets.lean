import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalLabels
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.BranchTargets
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRTarget
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Neighbor.CountingEquationTarget

/-! # Canonical Targets -/

namespace OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalTargets.CM

noncomputable section

/-! Each original native quotient labels the same actual branch target
on a common evaluation field. Its specialized equation point remains
the original NeighborCounting reduced target, with no new target-matching input. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
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

variable {L' : Type} [Field L'] [Algebra (ArithmeticBase.CM.Generic.F q) L']
  [Algebra (ArithmeticBase.CM.W (q := q)) L'] [IsScalarTower (ArithmeticBase.CM.W (q := q)) (ArithmeticBase.CM.Generic.F q) L']
  (V' : Isogenies.NeighborCounting.EvaluationDVRLifts.EvaluationDVR (ArithmeticBase.CM.W (q := q)) L') (σ : d.carrier →ₐ[ArithmeticBase.CM.Generic.F q] L')

local notation "extTarget" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationDVRTarget.CM.target V V' σ (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.arithmeticMap (j := j) hden) Q.target

variable
  (hg : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).IsGoodCompletelySplitPrime)
  (hgeometry : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).HasIntegralModelGeometry)
  (hIsogenyQuotient : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

include hg hgeometry hIsogenyQuotient in
theorem target_projection : (extTarget).map =
    (((HD).correspondence (typ i)).endpoint
      (CanonicalLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
        active multiplicative hTorsionQuotient d σ hIsogenyQuotient i β)).left ≫
      pullback.fst (M.integral a).toOver.hom M.arithmetic.generic := by
  have he := congrArg (fun y => y.left ≫ pullback.fst (M.integral a).toOver.hom M.arithmetic.generic)
    (CanonicalLabels.CM.endpoint_eq M hM j hsplit R labels hlabels a hden p l C
      active multiplicative hTorsionQuotient d σ hIsogenyQuotient i β)
  have hp := BranchTargets.CM.target_projection M hM j hsplit R labels hlabels a hden p l C
    active multiplicative hTorsionQuotient d V i β Q hg hgeometry hIsogenyQuotient
  exact (EvaluationDVRTarget.CM.target_map V V' σ (ArithmeticBase.CM.arithmeticMap (j := j) hden) Q.target).trans
    ((congrArg (Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ ·) hp).trans
      ((Category.assoc _ _ _).symm.trans he.symm))

include hg hgeometry hIsogenyQuotient in
theorem target_point_eq :
    EvaluatedTargetPoint.CM.point M hM j hsplit R labels hlabels a hden V' extTarget =
      ((HD).correspondence (typ i)).endpoint
        (CanonicalLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
          active multiplicative hTorsionQuotient d σ hIsogenyQuotient i β) :=
  ReductionPointProjection.CM.Recovery.point_eq_of_projection M.arithmetic.generic (M.integral a).toOver
    (Over.mk (EvaluationGenericTest.CM.originalBase (L := L') j)) _ _
    ((EvaluatedTargetPoint.CM.point_projection M hM j hsplit R labels hlabels a hden V' extTarget).trans
      (target_projection M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d V
        i β Q V' σ hg hgeometry hIsogenyQuotient))

variable {g : ℕ} (G : AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme g M.arithmetic.base) (α : (M.integral a).toOver ⟶ G.scheme)

theorem equationPoint_eq :
    Neighbor.CountingEquationTarget.CM.equationPoint M hM j hsplit R labels hlabels a hden V' extTarget G α =
      Q.target.specialPoint (Isogenies.NeighborCounting.ConstructedEvaluation.Lifts.evaluation_residueCompatible V
        (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden)) :=
  (Neighbor.CountingEquationTarget.CM.point_eq M hM j hsplit R labels hlabels a hden V' extTarget G α).trans
    (EvaluationDVRTarget.CM.specialPoint_eq V V' σ (ArithmeticBase.CM.arithmeticMap (j := j) hden) Q.target
      (ArithmeticBase.CM.residueIso (q := q)) (FrobeniusKernelLifts.CM.residueCompatible M hM j hsplit R labels hlabels a hden))

end

end OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalTargets.CM
