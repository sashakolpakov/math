import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ExtendedLabels
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldExtension
import OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.BranchEnumeration

/-! # Canonical Labels -/

namespace OAI

noncomputable section

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalLabels.CM

/-! Retain the original evaluated labels and targets on the canonical
arithmetic test of a further evaluation field. Actual precomposition
preserves each endpoint, while the complete parameter enumeration proves
that no branches are lost. -/

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

variable {L' : Type} [Field L'] [Algebra (ArithmeticBase.CM.Generic.F q) L'] (σ : d.carrier →ₐ[ArithmeticBase.CM.Generic.F q] L')
  (hIsogenyQuotient : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

local notation "base" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.EvaluationGenericTest.CM.originalBase (L := d.carrier) j
local notation "extPoint" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.FieldPointDescent.CM.testMap σ.toRingHom base ≫ z
local notation "iso" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.AlgebraFieldTest.CM.testIso (OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.ArithmeticBase.CM.Generic.numberFieldBase j) σ
local notation "newPoint" => OAI.AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.FieldPoint.CM.fieldPoint (L := L') (OAI.AlgebraicGeometry.PELModuli.IntegralModel.PEL.Has.IntegralPELSpread.toOver (M.integral a)) sl

def originalLabels (i : Fin 3) :=
  BranchLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
    active multiplicative hTorsionQuotient d hIsogenyQuotient i

def extendedLabels (i : Fin 3) : ULift (Fin (d.count (some i))) ≃
    ((HD).correspondence (typ i)).Fiber extPoint :=
  Finite.BranchEnumeration.CM.extendedLabels ((HD).correspondence (typ i))
    (FieldPointDescent.CM.testMap σ.toRingHom base) z (originalLabels M hM j hsplit R labels hlabels a hden p l C
      active multiplicative hTorsionQuotient d hIsogenyQuotient i)
    (ExtendedLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
      active multiplicative hTorsionQuotient d σ.toRingHom hIsogenyQuotient i)

def branchEquiv (i : Fin 3) : ULift (Fin (d.count (some i))) ≃
    ((HD).correspondence (typ i)).Fiber newPoint :=
  BranchEnumeration.CM.TestIso.labels ((HD).correspondence (typ i)) iso extPoint
    (extendedLabels M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d σ hIsogenyQuotient i)
    (FieldExtension.CM.reindexed_fieldPoint (M.integral a).toOver sl σ)

theorem endpoint_eq (i : Fin 3) (β : ULift (Fin (d.count (some i)))) :
    ((HD).correspondence (typ i)).endpoint
      (branchEquiv M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d σ hIsogenyQuotient i β) =
    AlgebraFieldTest.CM.map (ArithmeticBase.CM.Generic.numberFieldBase j) σ ≫
      ((HD).correspondence (typ i)).endpoint
        (originalLabels M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d hIsogenyQuotient i β) := by
  have h₁ := BranchEnumeration.CM.TestIso.labels_endpoint ((HD).correspondence (typ i)) iso extPoint
    (extendedLabels M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d σ hIsogenyQuotient i)
    (FieldExtension.CM.reindexed_fieldPoint (M.integral a).toOver sl σ) β
  have h₂ := Finite.BranchEnumeration.CM.extendedLabels_endpoint ((HD).correspondence (typ i))
    (FieldPointDescent.CM.testMap σ.toRingHom base) z
    (originalLabels M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d hIsogenyQuotient i)
    (ExtendedLabels.CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
      active multiplicative hTorsionQuotient d σ.toRingHom hIsogenyQuotient i) β
  exact h₁.trans ((congrArg ((iso).hom ≫ ·) h₂).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ ((HD).correspondence (typ i)).endpoint
        (originalLabels M hM j hsplit R labels hlabels a hden p l C active multiplicative hTorsionQuotient d hIsogenyQuotient i β))
        (AlgebraFieldTest.CM.map_eq (ArithmeticBase.CM.Generic.numberFieldBase j) σ).symm)))

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalLabels.CM

namespace AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalLabels.CM.Geometric

/-! The original finite branch labels remain complete on a canonical
geometric test of the common field. The source equality is the proved
naturality of its original Witt lift. -/

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

variable {L' : Type} [Field L'] [Algebra (ArithmeticBase.CM.Generic.F q) L'] (σ : d.carrier →ₐ[ArithmeticBase.CM.Generic.F q] L')
  (hIsogenyQuotient : (PELSource.CM.heckeData M a C
    (fun w => j.localCharacter M.extendedEmbedding (labels w))).RealizesIsogenyQuotient)

variable {L'' : Type} [Field L''] [Algebra (ArithmeticBase.CM.Generic.F q) L''] (τ : L' →ₐ[ArithmeticBase.CM.Generic.F q] L'')

def branchEquiv (i : Fin 3) : ULift (Fin (d.count (some i))) ≃
    ((HD).correspondence (typ i)).Fiber
      (AlgebraFieldTest.CM.map (ArithmeticBase.CM.Generic.numberFieldBase j) τ ≫
        FieldPoint.CM.fieldPoint (L := L') (M.integral a).toOver sl) :=
  (CM.branchEquiv M hM j hsplit R labels hlabels a hden p l C
    active multiplicative hTorsionQuotient d (τ.comp σ) hIsogenyQuotient i).trans
      (BranchEnumeration.CM.TestIso.sourceEquiv ((HD).correspondence (typ i))
        (FieldExtension.CM.fieldPoint_natural (M.integral a).toOver sl τ).symm)

end AlgebraicGeometry.HodgeConjecture.HeckeCycles.Witt.CanonicalLabels.CM.Geometric

end

end OAI
